#!/usr/bin/env python3
"""Safely assign factions per player slot in Cultures Nation Mod maps."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import shutil
import struct
import tempfile
from dataclasses import dataclass
from pathlib import Path


MAGIC_TYPE2 = 1021
MARKER = 1001
GAME_VERSION = "1.3.2"
MANIFEST_VERSION = 3
FACTIONS = {
    "vik": ("VIKING", 1),
    "fra": ("FRANK", 2),
    "byz": ("BYZANTINE", 3),
    "sar": ("SARACEN", 4),
    "egy": ("EGYPT", 7),
}
PROFILE_SUFFIX = re.compile(r"_(?:vik|fra|byz|sar|egy)$", re.IGNORECASE)
SUBMAP_NAME = re.compile(r"(?:[_ -]sub\d*|[_ -]sc\d+)$", re.IGNORECASE)
SYMBOLIC_PLAYER = re.compile(
    r"^(\s*player\s+(\d+)\s+#PLAYER_TYPE_(HUMAN|AI)\s+)"
    r"#TRIBE_TYPE_HUMAN_([A-Za-z_]+)(\s+.*)$",
    re.IGNORECASE,
)
NUMERIC_PLAYER = re.compile(
    r"^(\s*player\s+(\d+)\s+([12])\s+)(\d+)(\s+.*)$",
    re.IGNORECASE,
)
ANY_PLAYER = re.compile(r"^\s*player\s+(\d+)\s+", re.IGNORECASE)
MAP_TYPE = re.compile(r"^\s*maptype\s+([^\s/]+)", re.IGNORECASE)
FACTION_BY_TRIBE = {tribe.upper(): code for code, (tribe, _) in FACTIONS.items()}
FACTION_BY_ID = {tribe_id: code for code, (_, tribe_id) in FACTIONS.items()}


def crypt(data: bytes, *, encrypt: bool) -> bytes:
    result = bytearray(len(data))
    c, d = 71, 126
    for index, value in enumerate(data):
        result[index] = ((value ^ c) + 1) & 0xFF if encrypt else (((value - 1) & 0xFF) ^ c) & 0xFF
        c += d
        d += 33
    return bytes(result)


def unpack_cif(blob: bytes) -> list[str]:
    if len(blob) < 53:
        raise ValueError("CIF is shorter than its header")
    fields = struct.unpack_from("<10I", blob, 0)
    magic, zero, one, count_a, count_b, count_c, content_hint, marker, zero_b, index_len = fields
    if magic != MAGIC_TYPE2 or (zero, one, marker, zero_b) != (0, 1, MARKER, 0):
        raise ValueError("Unsupported CIF header")
    if not (count_a == count_b == count_c):
        raise ValueError("Inconsistent CIF entry counts")
    index_end = 40 + index_len
    if index_len != count_a * 4 or index_end + 13 > len(blob):
        raise ValueError("Invalid CIF index length")
    section_flag = blob[index_end]
    marker_b, zero_c, content_len = struct.unpack_from("<III", blob, index_end + 1)
    content_start = index_end + 13
    if (section_flag, marker_b, zero_c) != (1, MARKER, 0):
        raise ValueError("Invalid CIF content header")
    if content_start + content_len != len(blob) or content_hint != content_len:
        raise ValueError("Invalid CIF content length")
    index = crypt(blob[40:index_end], encrypt=False)
    content = crypt(blob[content_start:], encrypt=False)
    offsets = struct.unpack(f"<{count_a}I", index)
    lines: list[str] = []
    for offset in offsets:
        if offset + 1 >= len(content):
            raise ValueError("CIF entry offset is outside content")
        meta = content[offset]
        end = content.find(b"\0", offset + 1)
        if end < 0:
            raise ValueError("CIF entry has no terminator")
        text = content[offset + 1 : end].decode("latin-1")
        if meta == 1:
            lines.append(f"[{text}]")
        elif meta == 2:
            lines.append(text)
        else:
            raise ValueError("Unsupported CIF metadata")
    return lines


def pack_cif(lines: list[str]) -> bytes:
    index = bytearray()
    content = bytearray()
    for original in lines:
        line = original.strip()
        index.extend(struct.pack("<I", len(content)))
        if line.startswith("["):
            if not line.endswith("]"):
                raise ValueError(f"Invalid CIF section: {line}")
            content.append(1)
            line = line[1:-1]
        else:
            content.append(2)
        content.extend(line.encode("latin-1"))
        content.append(0)
    count = len(lines)
    encrypted_index = crypt(bytes(index), encrypt=True)
    encrypted_content = crypt(bytes(content), encrypt=True)
    header = struct.pack(
        "<10I", MAGIC_TYPE2, 0, 1, count, count, count,
        len(content), MARKER, 0, len(index),
    )
    middle = bytes([1]) + struct.pack("<III", MARKER, 0, len(content))
    return header + encrypted_index + middle + encrypted_content


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def atomic_write(path: Path, data: bytes) -> None:
    handle, temporary_name = tempfile.mkstemp(prefix=".cnmod-launcher-", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def resolve_map(root: Path, map_name: str) -> tuple[Path, Path]:
    root = root.resolve()
    maps_root = (root / "CnModMaps").resolve()
    if not maps_root.is_dir():
        raise ValueError(f"Missing CnModMaps: {maps_root}")
    map_dir = (maps_root / map_name).resolve()
    if map_dir.parent != maps_root or not map_dir.is_dir():
        raise ValueError("Map must be a direct child of CnModMaps")
    if not (map_dir / "map.dat").is_file():
        raise ValueError("Selected directory has no map.dat")
    return maps_root, map_dir


def get_config_files(map_dir: Path) -> list[Path]:
    result = sorted(map_dir.glob("*.inc")) + sorted(map_dir.glob("*.ini"))
    map_cif = map_dir / "map.cif"
    if map_cif.is_file():
        result.append(map_cif)
    return sorted(set(result))


def inspect_lines(lines: list[str]) -> tuple[list[int], str]:
    section = ""
    symbolic: list[int] = []
    numeric: list[int] = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].lower()
            continue
        match = SYMBOLIC_PLAYER.match(line)
        if match and match.group(3).upper() == "HUMAN":
            symbolic.append(int(match.group(2)))
            continue
        if section == "playerdata":
            match = NUMERIC_PLAYER.match(line)
            if match and match.group(3) == "1":
                numeric.append(int(match.group(2)))
    if symbolic:
        return sorted(set(symbolic)), "symbolic"
    if numeric:
        return sorted(set(numeric)), "numeric"
    return [], "dynamic"


def inspect_all_player_slots(lines: list[str]) -> list[int]:
    section = ""
    slots: list[int] = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].lower()
            continue
        if section == "playerdata":
            match = ANY_PLAYER.match(line)
            if match:
                slots.append(int(match.group(1)))
    return sorted(set(slots))


def inspect_players(lines: list[str]) -> list[dict]:
    section = ""
    players: dict[int, dict] = {}
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].lower()
            continue
        match = SYMBOLIC_PLAYER.match(line)
        if match:
            slot = int(match.group(2))
            tribe = match.group(4).upper()
            players[slot] = {
                "slot": slot,
                "type": match.group(3).lower(),
                "faction": FACTION_BY_TRIBE.get(tribe),
                "tribe": tribe,
            }
            continue
        if section == "playerdata":
            match = NUMERIC_PLAYER.match(line)
            if match:
                slot = int(match.group(2))
                tribe_id = int(match.group(4))
                players[slot] = {
                    "slot": slot,
                    "type": "human" if match.group(3) == "1" else "ai",
                    "faction": FACTION_BY_ID.get(tribe_id),
                    "tribeId": tribe_id,
                }
    return [players[slot] for slot in sorted(players)]


def inspect_map_category(lines: list[str]) -> str | None:
    section = ""
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith(("//", ";")):
            continue
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].lower()
            continue
        match = MAP_TYPE.match(line)
        if not match:
            continue
        value = match.group(1).upper()
        if "MULTI_PLAYER" in value or value == "4":
            return "multiplayer"
        if "SINGLE_PLAYER_CAMPAIGN" in value or value == "1":
            return "campaign"
        if "SINGLE_PLAYER" in value or value == "2":
            return "singleplayer"
        if section == "misc_maptype":
            return "singleplayer"
    return None


def inspect_map(map_dir: Path) -> dict:
    slots: list[int] = []
    all_slots: list[int] = []
    source_type = "dynamic"
    category = None
    player_records: dict[int, dict] = {}
    for path in get_config_files(map_dir):
        try:
            if path.suffix.lower() == ".cif":
                lines = unpack_cif(path.read_bytes())
                current_slots, current_type = inspect_lines(lines)
                if current_slots:
                    current_type = "compiled"
            else:
                lines = path.read_text(encoding="latin-1").splitlines()
                current_slots, current_type = inspect_lines(lines)
        except (OSError, ValueError):
            continue
        if current_slots:
            slots.extend(current_slots)
            source_type = current_type if source_type == "dynamic" else source_type
        all_slots.extend(inspect_all_player_slots(lines))
        for record in inspect_players(lines):
            player_records[record["slot"]] = record
        if category is None:
            category = inspect_map_category(lines)
    if category is None:
        category = "campaign" if SUBMAP_NAME.search(map_dir.name) else "singleplayer"
    return {
        "name": map_dir.name,
        "humanSlots": sorted(set(slots)),
        "playerSlots": sorted(set(all_slots)),
        "playerCount": len(set(all_slots)),
        "players": [player_records[slot] for slot in sorted(player_records)],
        "sourceType": source_type,
        "category": category,
        "isSubmap": bool(SUBMAP_NAME.search(map_dir.name)),
        "configFiles": len(get_config_files(map_dir)),
    }


def list_maps(root: Path) -> list[dict]:
    maps_root = (root.resolve() / "CnModMaps").resolve()
    result = []
    for map_dir in sorted(maps_root.iterdir(), key=lambda item: item.name.casefold()):
        if not map_dir.is_dir() or not (map_dir / "map.dat").is_file():
            continue
        if PROFILE_SUFFIX.search(map_dir.name):
            continue
        result.append(inspect_map(map_dir))
    return result


def patch_owned_commands(line: str, slot: int, tribe: str) -> str:
    culture = tribe.lower()
    # Direct map commands. Keep spacing and all parameters after the culture/house id.
    line = re.sub(
        rf'^(\s*set(?:human|humanx|vehicle)\s+{slot}\s+")[A-Za-z_]+(".*)$',
        rf'\1{culture}\2', line, flags=re.IGNORECASE,
    )
    line = re.sub(
        rf'^(\s*sethouse\s+{slot}\s+")[A-Za-z_]+(\s+[^\"]+".*)$',
        rf'\1{culture}\2', line, flags=re.IGNORECASE,
    )
    # Mission result commands use the player id immediately after the quoted command.
    line = re.sub(
        rf'^(\s*result\s+"Set(?:Human|HumanX|Vehicle)"\s+{slot}\s+")[A-Za-z_]+(".*)$',
        rf'\1{culture}\2', line, flags=re.IGNORECASE,
    )
    line = re.sub(
        rf'^(\s*result\s+"SetHouse"\s+{slot}\s+")[A-Za-z_]+(\s+[^\"]+".*)$',
        rf'\1{culture}\2', line, flags=re.IGNORECASE,
    )
    return line


def patch_lines(lines: list[str], slot: int, tribe: str, tribe_id: int) -> tuple[list[str], int]:
    section = ""
    changed = 0
    output: list[str] = []
    for original in lines:
        line = original
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            section = stripped[1:-1].lower()
        match = SYMBOLIC_PLAYER.match(line)
        if match and int(match.group(2)) == slot:
            line = f"{match.group(1)}#TRIBE_TYPE_HUMAN_{tribe}{match.group(5)}"
        elif section == "playerdata":
            match = NUMERIC_PLAYER.match(line)
            if match and int(match.group(2)) == slot:
                line = f"{match.group(1)}{tribe_id}{match.group(5)}"
        line = patch_owned_commands(line, slot, tribe)
        if line != original:
            changed += 1
        output.append(line)
    return output, changed


def state_for(root: Path, map_name: str) -> Path:
    key = hashlib.sha1(map_name.encode("utf-8")).hexdigest()[:16]
    return root.resolve() / "CnModLauncherData" / "map-backups" / GAME_VERSION / key


def current_hashes(map_dir: Path) -> dict[str, str]:
    return {path.name: sha256(path) for path in get_config_files(map_dir)}


def baseline_files(map_dir: Path, state: Path, manifest: dict) -> list[tuple[Path, bytes]]:
    if (manifest.get("version") != MANIFEST_VERSION
            or manifest.get("gameVersion") != GAME_VERSION
            or manifest.get("mapName") != map_dir.name):
        raise ValueError("Kopia zapasowa nie należy do tej mapy i wersji CnMod.")
    if (sha256(map_dir / "map.dat") != manifest.get("mapDataSha256")
            or current_hashes(map_dir) != manifest.get("currentHashes")):
        raise ValueError(
            "Pliki mapy zmieniły się poza launcherem. Zatrzymano zapis, aby nie "
            "nadpisać aktualizacji starą kopią. Zachowaj folder kopii mapy i "
            "przenieś go poza map-backups/1.3.2 przed utworzeniem nowej bazy."
        )
    result = []
    for entry in manifest["files"]:
        relative = Path(entry["relative"])
        if relative.is_absolute() or ".." in relative.parts or len(relative.parts) != 1:
            raise ValueError("Unsafe path in map manifest")
        backup = (state / "original" / relative).resolve()
        target = (map_dir / relative).resolve()
        if state.resolve() not in backup.parents or map_dir.resolve() not in target.parents:
            raise ValueError("Manifest path escaped its allowed directory")
        if not backup.is_file() or sha256(backup) != entry["sha256"]:
            raise ValueError(f"Invalid backup: {backup}")
        result.append((target, backup.read_bytes()))
    return result


def commit_files(files: list[tuple[Path, bytes]]) -> None:
    previous = [(path, path.read_bytes()) for path, _ in files]
    try:
        for path, data in files:
            atomic_write(path, data)
    except BaseException:
        for path, data in previous:
            atomic_write(path, data)
        raise


def restore_baseline(root: Path, map_dir: Path, state: Path, manifest: dict) -> None:
    commit_files(baseline_files(map_dir, state, manifest))


def ensure_baseline(root: Path, map_dir: Path) -> tuple[Path, dict]:
    state = state_for(root, map_dir.name)
    manifest_path = state / "manifest.json"
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        baseline_files(map_dir, state, manifest)
        return state, manifest
    state.mkdir(parents=True, exist_ok=False)
    entries = []
    for source in get_config_files(map_dir):
        relative = source.relative_to(map_dir)
        backup = state / "original" / relative
        backup.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, backup)
        entries.append({"relative": str(relative), "sha256": sha256(backup)})
    manifest = {"version": MANIFEST_VERSION, "gameVersion": GAME_VERSION,
                "mapName": map_dir.name, "files": entries,
                "mapDataSha256": sha256(map_dir / "map.dat"),
                "currentHashes": current_hashes(map_dir)}
    atomic_write(manifest_path, json.dumps(manifest, indent=2, ensure_ascii=False).encode("utf-8"))
    return state, manifest


def activate(
    root: Path,
    map_name: str,
    faction: str | None = None,
    players: str = "human",
    assignments: dict[int, str] | None = None,
) -> dict:
    if faction is not None and faction not in FACTIONS:
        raise ValueError(f"Unsupported faction: {faction}")
    if faction is None and not assignments:
        raise ValueError("Provide --faction or --assignments")
    _, map_dir = resolve_map(root, map_name)
    metadata = inspect_map(map_dir)
    human_slot = 0 if 0 in metadata["humanSlots"] else (metadata["humanSlots"][0] if metadata["humanSlots"] else 0)
    if assignments:
        slot_factions = {int(slot): code for slot, code in assignments.items()}
        invalid = sorted({code for code in slot_factions.values() if code not in FACTIONS})
        if invalid:
            raise ValueError(f"Unsupported factions in assignments: {', '.join(invalid)}")
        known_slots = set(metadata["playerSlots"])
        if known_slots:
            invalid_slots = sorted(set(slot_factions) - known_slots)
            if invalid_slots:
                raise ValueError(f"Map has no player slots: {invalid_slots}")
    else:
        slots = metadata["playerSlots"] if players == "all" else [human_slot]
        if not slots:
            slots = [human_slot]
        slot_factions = {slot: faction for slot in slots}
    state, manifest = ensure_baseline(root, map_dir)
    files_changed = 0
    lines_changed = 0
    pending = []
    for path, raw in baseline_files(map_dir, state, manifest):
        if path.suffix.lower() == ".cif":
            original_lines = unpack_cif(raw)
            patched = original_lines
            count = 0
            for slot, slot_faction in slot_factions.items():
                tribe, tribe_id = FACTIONS[slot_faction]
                patched, slot_count = patch_lines(patched, slot, tribe, tribe_id)
                count += slot_count
            data = pack_cif(patched) if count else raw
        else:
            newline = "\r\n" if b"\r\n" in raw else "\n"
            had_final_newline = raw.endswith((b"\r", b"\n"))
            original_lines = raw.decode("latin-1").splitlines()
            patched = original_lines
            count = 0
            for slot, slot_faction in slot_factions.items():
                tribe, tribe_id = FACTIONS[slot_faction]
                patched, slot_count = patch_lines(patched, slot, tribe, tribe_id)
                count += slot_count
            if count:
                text = newline.join(patched) + (newline if had_final_newline else "")
                data = text.encode("latin-1")
            else:
                data = raw
        pending.append((path, data))
        if count:
            files_changed += 1
            lines_changed += count
    manifest["activeFaction"] = faction
    manifest["playerSlots"] = sorted(slot_factions)
    manifest["playerScope"] = "custom" if assignments else players
    manifest["playerAssignments"] = {str(slot): code for slot, code in sorted(slot_factions.items())}
    manifest["sourceType"] = metadata["sourceType"]
    manifest["filesChanged"] = files_changed
    manifest["linesChanged"] = lines_changed
    manifest["currentHashes"] = {path.name: hashlib.sha256(data).hexdigest().upper() for path, data in pending}
    pending.append((state / "manifest.json", json.dumps(manifest, indent=2, ensure_ascii=False).encode("utf-8")))
    commit_files(pending)
    return {
        "map": map_name,
        "faction": faction,
        "playerSlots": sorted(slot_factions),
        "playerScope": "custom" if assignments else players,
        "playerAssignments": {str(slot): code for slot, code in sorted(slot_factions.items())},
        "sourceType": metadata["sourceType"],
        "filesChanged": files_changed,
        "linesChanged": lines_changed,
        "explicitPlayerDefinition": bool(metadata["humanSlots"]),
    }


def restore(root: Path, map_name: str) -> dict:
    _, map_dir = resolve_map(root, map_name)
    state = state_for(root, map_name)
    manifest_path = state / "manifest.json"
    if not manifest_path.is_file():
        raise ValueError("No launcher backup exists for this map")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    pending = baseline_files(map_dir, state, manifest)
    manifest["activeFaction"] = None
    manifest["playerAssignments"] = {}
    manifest["currentHashes"] = {path.name: hashlib.sha256(data).hexdigest().upper() for path, data in pending}
    pending.append((manifest_path, json.dumps(manifest, indent=2, ensure_ascii=False).encode("utf-8")))
    commit_files(pending)
    return {"map": map_name, "restored": True, "files": len(manifest["files"])}


def validate_all(root: Path) -> dict:
    records = list_maps(root)
    failures = []
    profiles_checked = 0
    format_counts: dict[str, int] = {}
    maps_root = root.resolve() / "CnModMaps"
    for record in records:
        format_counts[record["sourceType"]] = format_counts.get(record["sourceType"], 0) + 1
        if not record["humanSlots"]:
            failures.append({"map": record["name"], "reason": "no explicit human player"})
            continue
        slot = 0 if 0 in record["humanSlots"] else record["humanSlots"][0]
        map_dir = maps_root / record["name"]
        zero_change_profiles = 0
        for faction, (tribe, tribe_id) in FACTIONS.items():
            profiles_checked += 1
            changes = 0
            try:
                for path in get_config_files(map_dir):
                    lines = unpack_cif(path.read_bytes()) if path.suffix.lower() == ".cif" else path.read_text(encoding="latin-1").splitlines()
                    _, count = patch_lines(lines, slot, tribe, tribe_id)
                    changes += count
            except (OSError, ValueError) as error:
                failures.append({"map": record["name"], "faction": faction, "reason": str(error)})
                continue
            if changes == 0:
                zero_change_profiles += 1
        # At most one faction can already match the untouched source map.
        if zero_change_profiles > 1:
            failures.append({"map": record["name"], "reason": f"{zero_change_profiles} profiles make no change"})
    return {
        "maps": len(records),
        "factions": len(FACTIONS),
        "profilesChecked": profiles_checked,
        "formats": format_counts,
        "failures": failures,
        "ok": not failures,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    listing = sub.add_parser("list")
    listing.add_argument("--root", type=Path, required=True)
    activation = sub.add_parser("activate")
    activation.add_argument("--root", type=Path, required=True)
    activation.add_argument("--map", required=True)
    activation.add_argument("--faction", choices=sorted(FACTIONS))
    activation.add_argument("--players", choices=("human", "all"), default="human")
    activation.add_argument(
        "--assignments",
        help='JSON object mapping player slots to faction codes, e.g. {"0":"egy","1":"vik"}',
    )
    activation.add_argument(
        "--assignments-b64",
        help="UTF-8 JSON assignments encoded as Base64 (launcher-safe transport)",
    )
    restoration = sub.add_parser("restore")
    restoration.add_argument("--root", type=Path, required=True)
    restoration.add_argument("--map", required=True)
    validation = sub.add_parser("validate")
    validation.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "list":
        result = list_maps(args.root)
    elif args.command == "activate":
        assignment_data = None
        raw_assignments = args.assignments
        if args.assignments_b64:
            raw_assignments = base64.b64decode(args.assignments_b64).decode("utf-8")
        if raw_assignments:
            parsed = json.loads(raw_assignments)
            if not isinstance(parsed, dict):
                raise ValueError("--assignments must be a JSON object")
            assignment_data = {int(slot): str(code) for slot, code in parsed.items()}
        result = activate(args.root, args.map, args.faction, args.players, assignment_data)
    elif args.command == "restore":
        result = restore(args.root, args.map)
    else:
        result = validate_all(args.root)
    # ASCII JSON remains lossless through legacy Windows console code pages.
    print(json.dumps(result, ensure_ascii=True))


if __name__ == "__main__":
    main()
