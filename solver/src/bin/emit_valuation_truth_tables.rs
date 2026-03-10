use std::io::{self, Write};

fn valuation_truth_table_hex(pos: usize) -> String {
    const BIT_COUNT: usize = 65536;
    const NIBBLE_COUNT: usize = BIT_COUNT / 4;

    let mut out = String::with_capacity(2 + NIBBLE_COUNT + 6);
    out.push_str("0x");

    for nibble_idx in (0..NIBBLE_COUNT).rev() {
        let base = nibble_idx * 4;
        let mut nibble = 0u8;
        for bit in 0..4 {
            let idx = base + bit;
            if ((idx >> pos) & 1) == 1 {
                nibble |= 1 << bit;
            }
        }
        out.push(std::char::from_digit(nibble as u32, 16).unwrap().to_ascii_uppercase());
    }

    out.push_str("#65536");
    out
}

fn main() -> io::Result<()> {
    let stdout = io::stdout();
    let mut output = stdout.lock();

    writeln!(
        output,
        "-- DO NOT EDIT MANUALLY: generated valuation truth tables for 4-world, 4-variable valuations"
    )?;
    writeln!(output)?;
    writeln!(output, "import Init.Data.BitVec.Lemmas")?;
    writeln!(output, "import Mathlib.Tactic.FinCases")?;
    writeln!(output)?;
    writeln!(output, "namespace KripkeGameStrategy.Generated")?;
    writeln!(output)?;
    writeln!(output, "abbrev ValuationTruthTable := BitVec 65536")?;
    writeln!(output)?;
    writeln!(output, "def valuationTruthTables : Array ValuationTruthTable := #[")?;
    for pos in 0..16 {
        writeln!(output, "  {},", valuation_truth_table_hex(pos))?;
    }
    writeln!(output, "]")?;
    writeln!(output)?;
    writeln!(output, "theorem valuationTruthTables_spec (pos : Fin 16) :")?;
    writeln!(
        output,
        "    ∀ idx : Fin 65536, valuationTruthTables[pos][idx] = (BitVec.ofFin (w := 16) idx)[pos] := by"
    )?;
    writeln!(output, "  fin_cases pos <;> native_decide")?;
    writeln!(output)?;
    writeln!(output, "end KripkeGameStrategy.Generated")?;

    Ok(())
}
