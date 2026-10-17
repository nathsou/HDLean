import HDLean.Rtl.Syntax

/-!
# Every word-level operator, for backend checks

Not a challenge: a module that uses each operator once (division and remainder
by a two-bit divisor, so that division by zero is frequent), a register with a
synchronous reset and a memory with two write ports. `check_backends.py` runs
its word SystemVerilog, its word RTLIL (through Yosys) and its bit-blasted
netlist against the Lean trace of `Design.step`.
-/
namespace HDLean.RtlOps
open HDLean.Rtl

private def c (w : Nat) (op : Op) : Cell := ⟨w, op⟩

def module : Module :=
  { name := .ofString "ops"
    inputs := #[⟨.ofString "x", 8⟩, ⟨.ofString "y", 8⟩, ⟨.ofString "s", 3⟩, ⟨.ofString "d", 2⟩, ⟨.ofString "sel", 1⟩]
    outputs := #[⟨.ofString "o_const", 5⟩, ⟨.ofString "o_not", 6⟩, ⟨.ofString "o_neg", 7⟩, ⟨.ofString "o_and", 8⟩,
      ⟨.ofString "o_or", 9⟩, ⟨.ofString "o_xor", 10⟩, ⟨.ofString "o_nand", 11⟩, ⟨.ofString "o_nor", 12⟩,
      ⟨.ofString "o_xnor", 13⟩, ⟨.ofString "o_add", 14⟩, ⟨.ofString "o_sub", 15⟩, ⟨.ofString "o_mul", 16⟩,
      ⟨.ofString "o_div", 18⟩, ⟨.ofString "o_mod", 19⟩, ⟨.ofString "o_shl", 20⟩, ⟨.ofString "o_shr", 21⟩,
      ⟨.ofString "o_sshr", 22⟩, ⟨.ofString "o_eq", 23⟩, ⟨.ofString "o_ne", 24⟩, ⟨.ofString "o_ult", 25⟩,
      ⟨.ofString "o_ule", 26⟩, ⟨.ofString "o_slt", 27⟩, ⟨.ofString "o_sle", 28⟩, ⟨.ofString "o_cat2", 34⟩,
      ⟨.ofString "o_mux", 29⟩, ⟨.ofString "o_slice", 30⟩,
      ⟨.ofString "o_concat", 32⟩, ⟨.ofString "o_zext", 33⟩, ⟨.ofString "o_sext", 35⟩, ⟨.ofString "o_reg", 36⟩,
      ⟨.ofString "o_mem", 39⟩]
    cells := #[
      c 8 (.input 0), c 8 (.input 1), c 3 (.input 2), c 2 (.input 3), c 1 (.input 4),     -- 0..4
      c 8 (.const 0xA5),                                                                  -- 5
      c 8 (.not 0), c 8 (.neg 0),                                                         -- 6, 7
      c 8 (.bin .and 0 1), c 8 (.bin .or 0 1), c 8 (.bin .xor 0 1), c 8 (.bin .nand 0 1),  -- 8..11
      c 8 (.bin .nor 0 1), c 8 (.bin .xnor 0 1), c 8 (.bin .add 0 1), c 8 (.bin .sub 0 1), -- 12..15
      c 8 (.bin .mul 0 1),                                                                -- 16
      c 8 (.zext 3),                                                                      -- 17: divisor
      c 8 (.bin .udiv 0 17), c 8 (.bin .umod 0 17),                                       -- 18, 19
      c 8 (.bin .shl 0 2), c 8 (.bin .lshr 0 2), c 8 (.bin .ashr 0 2),                    -- 20..22
      c 1 (.cmp .eq 8 0 1), c 1 (.cmp .ne 8 0 1), c 1 (.cmp .ult 8 0 1),                  -- 23..25
      c 1 (.cmp .ule 8 0 1), c 1 (.cmp .slt 8 0 1), c 1 (.cmp .sle 8 0 1),                -- 26..28
      c 8 (.mux 4 0 1),                                                                   -- 29
      c 4 (.slice 0 2),                                                                   -- 30
      c 4 (.slice 1 4),                                                                   -- 31
      c 8 (.concat 30 31 4),                                                              -- 32
      c 12 (.zext 30),                                                                    -- 33
      c 2 (.concat 23 24 1),                                                              -- 34
      c 12 (.sext 30 4),                                                                  -- 35
      c 8 (.reg 0),                                                                       -- 36
      c 4 (.slice 1 0),                                                                   -- 37: memory address
      c 4 (.slice 0 0),                                                                   -- 38: read address
      c 8 (.memRead 0 38)]                                                                -- 39
    regs := #[⟨.ofString "acc", 8, .sync 0x3C, 14⟩]
    mems := #[⟨.ofString "ram", 4, 8, #[⟨4, 37, 0⟩, ⟨4, 38, 1⟩]⟩] }

def design : Design := ⟨#[module]⟩

end HDLean.RtlOps
