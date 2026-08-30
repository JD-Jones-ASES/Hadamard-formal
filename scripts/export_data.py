#!/usr/bin/env python3
"""Export pinned Hadamard-T witnesses as deterministic Lean definitions.

The exporter intentionally uses only the Python standard library.  It verifies
the source files byte-for-byte against the SHA-256 pins below before parsing
them, so a changed or substituted source cannot silently alter the Lean data.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import NoReturn


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPOSITORY_ROOT / "HadamardFormal" / "Data" / "Generated.lean"

SOURCE_PINS = {
    "data/T103.json": "cf59cb40fcdc74f9309161ad2d50ddd7ad462446da365efb527de0dd4e295a06",
    "data/T163.json": "285557b7fc0f846af4fcec2e83d5d97eabcff3b82b2171bd0a6bdf32f8d27a4d",
    "data/williamson-quadruples.json": "515dac963269e31694445c5ad7635b001e16b3ea3cdb58fa8ee12eaae47e0446",
    "data/williamson-13.json": "249ba0919c5f0b82faab5d6c248a1a2ab18107d5a6ee2175195236fc3509935f",
}

WILLIAMSON_ORDERS = (7, 11, 13, 17, 19, 23, 29)


class ExportError(ValueError):
    """A pinned source is missing, changed, or has an unexpected schema."""


def fail(message: str) -> NoReturn:
    raise ExportError(message)


def load_pinned_json(source_root: Path, relative_path: str) -> object:
    path = source_root / Path(relative_path)
    try:
        raw = path.read_bytes()
    except OSError as error:
        fail(f"cannot read {path}: {error}")

    actual_hash = hashlib.sha256(raw).hexdigest()
    expected_hash = SOURCE_PINS[relative_path]
    if actual_hash != expected_hash:
        fail(
            f"SHA-256 mismatch for {path}: expected {expected_hash}, "
            f"got {actual_hash}"
        )

    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        fail(f"{path} is not ASCII JSON: {error}")
    try:
        return json.loads(text)
    except json.JSONDecodeError as error:
        fail(f"invalid JSON in {path}: {error}")


def expect_mapping(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        fail(f"{label} must be a JSON object with string keys")
    return value


def expect_int(value: object, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{label} must be an integer")
    return value


def expect_list(value: object, label: str) -> list[object]:
    if not isinstance(value, list):
        fail(f"{label} must be a JSON array")
    return value


def decode_t_quadruple(document: object, expected_order: int, label: str) -> list[list[int]]:
    record = expect_mapping(document, label)
    order = expect_int(record.get("n"), f"{label}.n")
    if order != expected_order:
        fail(f"{label}.n must be {expected_order}, got {order}")

    classes_raw = expect_list(record.get("classes"), f"{label}.classes")
    signs_raw = expect_list(record.get("signs"), f"{label}.signs")
    if len(classes_raw) != order or len(signs_raw) != order:
        fail(
            f"{label} must have exactly {order} classes and signs, got "
            f"{len(classes_raw)} and {len(signs_raw)}"
        )

    classes = [expect_int(value, f"{label}.classes[{index}]") for index, value in enumerate(classes_raw)]
    signs = [expect_int(value, f"{label}.signs[{index}]") for index, value in enumerate(signs_raw)]
    bad_classes = [(index, value) for index, value in enumerate(classes) if value not in range(4)]
    bad_signs = [(index, value) for index, value in enumerate(signs) if value not in (-1, 1)]
    if bad_classes:
        fail(f"{label}.classes contains values outside 0..3: {bad_classes[:4]}")
    if bad_signs:
        fail(f"{label}.signs contains values outside -1,+1: {bad_signs[:4]}")

    quadruple = [[0 for _ in range(order)] for _ in range(4)]
    for index, (sequence, sign) in enumerate(zip(classes, signs)):
        quadruple[sequence][index] = sign

    support_sizes = record.get("support_sizes")
    if support_sizes is not None:
        sizes_raw = expect_list(support_sizes, f"{label}.support_sizes")
        sizes = [expect_int(value, f"{label}.support_sizes[{index}]") for index, value in enumerate(sizes_raw)]
        actual_sizes = [sum(value != 0 for value in row) for row in quadruple]
        if sizes != actual_sizes:
            fail(f"{label}.support_sizes is {sizes}, decoded support sizes are {actual_sizes}")

    row_sums = record.get("row_sums")
    if row_sums is not None:
        sums_raw = expect_list(row_sums, f"{label}.row_sums")
        sums = [expect_int(value, f"{label}.row_sums[{index}]") for index, value in enumerate(sums_raw)]
        actual_sums = [sum(row) for row in quadruple]
        if sums != actual_sums:
            fail(f"{label}.row_sums is {sums}, decoded row sums are {actual_sums}")

    return quadruple


def decode_williamson_quadruple(document: object, order: int, label: str) -> list[list[int]]:
    bank = expect_mapping(document, label)
    quadruples = expect_mapping(bank.get("quadruples"), f"{label}.quadruples")
    entry = expect_mapping(quadruples.get(str(order)), f"{label}.quadruples[{order!r}]")
    recorded_order = expect_int(entry.get("w"), f"{label}.quadruples[{order!r}].w")
    if recorded_order != order:
        fail(
            f"{label}.quadruples[{order!r}].w must be {order}, "
            f"got {recorded_order}"
        )

    rows_raw = expect_list(entry.get("rows"), f"{label}.quadruples[{order!r}].rows")
    if len(rows_raw) != 4:
        fail(f"{label}.quadruples[{order!r}].rows must contain four rows")

    rows: list[list[int]] = []
    for row_index, row in enumerate(rows_raw):
        if not isinstance(row, str):
            fail(f"{label}.quadruples[{order!r}].rows[{row_index}] must be a string")
        if len(row) != order:
            fail(
                f"{label}.quadruples[{order!r}].rows[{row_index}] must have "
                f"length {order}, got {len(row)}"
            )
        unexpected = sorted(set(row) - {"+", "-"})
        if unexpected:
            fail(
                f"{label}.quadruples[{order!r}].rows[{row_index}] contains "
                f"unexpected characters {unexpected}"
            )
        rows.append([1 if character == "+" else -1 for character in row])

    row_sums = entry.get("row_sums")
    if row_sums is not None:
        sums_raw = expect_list(row_sums, f"{label}.quadruples[{order!r}].row_sums")
        sums = [expect_int(value, f"{label}.row_sums[{index}]") for index, value in enumerate(sums_raw)]
        actual_sums = [sum(row) for row in rows]
        if sums != actual_sums:
            fail(
                f"{label}.quadruples[{order!r}].row_sums is {sums}, "
                f"decoded row sums are {actual_sums}"
            )

    return rows


def format_vector(values: list[int], indent: str, values_per_line: int = 16) -> list[str]:
    chunks = [values[index : index + values_per_line] for index in range(0, len(values), values_per_line)]
    lines = [f"{indent}#v["]
    for index, chunk in enumerate(chunks):
        suffix = "," if index + 1 < len(chunks) else ""
        lines.append(f"{indent}  {', '.join(str(value) for value in chunk)}{suffix}")
    lines.append(f"{indent}]")
    return lines


def format_quadruple(name: str, order: int, rows: list[list[int]], description: str) -> list[str]:
    if len(rows) != 4 or any(len(row) != order for row in rows):
        fail(f"internal shape error while formatting {name}")

    lines = [
        f"private def {name}Data : Vector (Vector Int {order}) 4 :=",
        "  #v[",
    ]
    for row_index, row in enumerate(rows):
        vector_lines = format_vector(row, "    ")
        if row_index + 1 < len(rows):
            vector_lines[-1] += ","
        lines.extend(vector_lines)
    lines.extend(
        [
            "  ]",
            "",
            f"/-- {description} -/",
            f"def {name} : Fin 4 → Fin {order} → Int := fun i j =>",
            f"  ({name}Data.get i).get j",
            "",
        ]
    )
    return lines


def format_t_certificate(name: str, order: int) -> list[str]:
    """Emit a kernel certificate sharded by cyclic shift.

    A single `decide` over the whole periodic predicate constructs one very
    large proof term.  Giving each shift its own declaration keeps replay in
    ordinary kernel reduction while bounding the elaborator's live state.
    """

    lines = [
        f"private theorem {name}_entries : ∀ i q, IsTEntry ({name} i q) := by",
        "  decide",
        "",
        f"private theorem {name}_support : ∀ q, supportCount {name} q = 1 := by",
        "  decide",
        "",
    ]
    for shift in range(order):
        index = f"(⟨{shift}, by decide⟩ : Fin {order})"
        lines.extend(
            [
                f"private theorem {name}_paf_{shift} :",
                f"    (∑ i, paf ({name} i) {index}) =",
                f"      ({order} : ℤ) * deltaZero {index} := by",
                "  rfl",
                "",
            ]
        )

    lines.extend(
        [
            f"/-- Kernel-reduced periodic T-matrix certificate for `{name}`. -/",
            f"theorem {name}_isTMatrixCertificate : IsTMatrixQuadruple {name} := by",
            "  unfold IsTMatrixQuadruple",
            f"  refine ⟨{name}_entries, {name}_support, ?_⟩",
            "  intro s",
            "  fin_cases s",
        ]
    )
    for shift in range(order):
        lines.append(f"  · exact {name}_paf_{shift}")
    lines.append("")
    return lines


def render(source_root: Path) -> str:
    documents = {
        relative_path: load_pinned_json(source_root, relative_path)
        for relative_path in SOURCE_PINS
    }

    definitions: list[tuple[str, int, list[list[int]], str]] = [
        (
            "t103",
            103,
            decode_t_quadruple(documents["data/T103.json"], 103, "data/T103.json"),
            "The generated four-sequence T-matrix witness of order 103.",
        ),
        (
            "t163",
            163,
            decode_t_quadruple(documents["data/T163.json"], 163, "data/T163.json"),
            "The generated four-sequence T-matrix witness of order 163.",
        ),
    ]

    base_bank = documents["data/williamson-quadruples.json"]
    order_13_bank = documents["data/williamson-13.json"]
    for order in WILLIAMSON_ORDERS:
        bank = order_13_bank if order == 13 else base_bank
        source_label = "data/williamson-13.json" if order == 13 else "data/williamson-quadruples.json"
        definitions.append(
            (
                f"w{order}",
                order,
                decode_williamson_quadruple(bank, order, source_label),
                f"The generated symmetric Williamson four-sequence witness of order {order}.",
            )
        )

    lines = [
        "/-",
        "This file is generated by scripts/export_data.py. Do not edit it by hand.",
        "The absolute --source-root is intentionally omitted so identical pinned inputs",
        "produce identical output on every machine.",
        "",
        "Pinned sources:",
    ]
    for relative_path, digest in SOURCE_PINS.items():
        lines.extend(
            [
                f"* Hadamard-T/{relative_path}",
                f"  SHA-256: {digest}",
            ]
        )
    lines.extend(
        [
            "-/",
            "",
            "import HadamardFormal.Defs",
            "",
            "namespace HadamardFormal.Data",
            "",
            "open HadamardFormalCore",
            "",
        ]
    )
    for name, order, rows, description in definitions:
        lines.extend(format_quadruple(name, order, rows, description))
    lines.extend(
        [
            "-- The kernel checks below evaluate fixed-length integer",
            "-- autocorrelation sums; the raised limits apply to this",
            "-- generated file only, and the style linter for file-level",
            "-- options is disabled here for the generated literals.",
            "set_option linter.style.setOption false",
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 0",
            "",
        ]
    )
    lines.extend(format_t_certificate("t103", 103))
    lines.extend(format_t_certificate("t163", 163))
    lines.extend(["end HadamardFormal.Data", ""])
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-root",
        type=Path,
        required=True,
        help="path to the Hadamard-T repository root (the directory containing data/)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"generated Lean file (default: {DEFAULT_OUTPUT})",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that --output already equals the deterministic generated content",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        content = render(args.source_root)
    except ExportError as error:
        raise SystemExit(f"export_data.py: error: {error}") from error

    encoded = content.encode("utf-8")
    output = args.output
    if args.check:
        try:
            existing = output.read_bytes()
        except OSError as error:
            raise SystemExit(f"export_data.py: error: cannot read {output}: {error}") from error
        if existing != encoded:
            raise SystemExit(f"export_data.py: error: generated output differs from {output}")
        print(f"up to date: {output} ({hashlib.sha256(encoded).hexdigest()})")
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.tmp-{os.getpid()}")
    try:
        temporary.write_bytes(encoded)
        os.replace(temporary, output)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
    print(
        f"wrote {output} ({len(encoded)} bytes, "
        f"SHA-256 {hashlib.sha256(encoded).hexdigest()})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
