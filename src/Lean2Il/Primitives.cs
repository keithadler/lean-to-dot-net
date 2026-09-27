using System.Reflection;
using System.Reflection.Emit;
using Tenet.Kernel;

namespace LeanToDotNet;

/// <summary>
/// The Lean constants compiled to a .NET operation instead of being unfolded.
///
/// Unfolding <c>Int.add</c> would reach a match on constructors and <c>Nat.add</c> a structural recursion, neither of
/// which is how anyone wants to add two numbers. Lean's own compiler makes the same substitution: these are the
/// operations its runtime implements natively (<c>@[extern]</c>), and Tenet's kernel evaluates <c>Nat</c>'s on literals
/// natively for the same reason. Each entry is the whole semantic claim lean2il makes about that constant, and the
/// test suite checks every one against Lean's own <c>#eval</c> output (<c>tests/PrimitiveTests.cs</c>).
/// </summary>
internal sealed record Primitive(Name Name, int[] Args, Kind Result, Action<ILGenerator> Emit, Type? ResultClr = null);

internal static class Primitives
{
    public static Dictionary<Name, Primitive> Build(Clr clr)
    {
        var t = new Dictionary<Name, Primitive>();
        void Add(string name, int[] args, Kind result, MethodInfo m) =>
            t[Name.Parse(name)] = new Primitive(Name.Parse(name), args, result, il => il.Emit(OpCodes.Call, m));
        void AddIl(string name, int[] args, Kind result, Action<ILGenerator> emit) =>
            t[Name.Parse(name)] = new Primitive(Name.Parse(name), args, result, emit);

        int[] a01 = [0, 1];
        int[] a0 = [0];

        // Nat
        Add("Nat.add", a01, Kind.Nat, clr.Big2("op_Addition"));
        Add("Nat.sub", a01, Kind.Nat, clr.Nat2("Sub"));
        Add("Nat.mul", a01, Kind.Nat, clr.Big2("op_Multiply"));
        Add("Nat.div", a01, Kind.Nat, clr.Nat2("Div"));
        Add("Nat.mod", a01, Kind.Nat, clr.Nat2("Mod"));
        Add("Nat.pow", a01, Kind.Nat, clr.Nat2("Pow"));
        Add("Nat.gcd", a01, Kind.Nat, clr.Nat2("Gcd"));
        Add("Nat.land", a01, Kind.Nat, clr.Big2("op_BitwiseAnd"));
        Add("Nat.lor", a01, Kind.Nat, clr.Big2("op_BitwiseOr"));
        Add("Nat.xor", a01, Kind.Nat, clr.Big2("op_ExclusiveOr"));
        Add("Nat.shiftLeft", a01, Kind.Nat, clr.Nat2("ShiftLeft"));
        Add("Nat.shiftRight", a01, Kind.Nat, clr.Nat2("ShiftRight"));
        Add("Nat.log2", a0, Kind.Nat, clr.Static(clr.LeanNat, "Log2", clr.BigInteger));
        Add("Nat.pred", a0, Kind.Nat, clr.Static(clr.LeanNat, "Pred", clr.BigInteger));
        Add("Nat.succ", a0, Kind.Nat, clr.Big1("op_Increment"));
        Add("Nat.beq", a01, Kind.Bool, clr.Big2("op_Equality"));
        Add("Nat.ble", a01, Kind.Bool, clr.Big2("op_LessThanOrEqual"));
        Add("Nat.blt", a01, Kind.Bool, clr.Big2("op_LessThan"));
        Add("Nat.decEq", a01, Kind.Bool, clr.Big2("op_Equality"));
        Add("Nat.decLe", a01, Kind.Bool, clr.Big2("op_LessThanOrEqual"));
        Add("Nat.decLt", a01, Kind.Bool, clr.Big2("op_LessThan"));

        // Int. Int.ofNat and Int.negSucc are its constructors; as operations they are a coercion and -(n + 1).
        AddIl("Int.ofNat", a0, Kind.Int, _ => { });
        Add("Int.negSucc", a0, Kind.Int, clr.Int1("NegSucc"));
        Add("Int.add", a01, Kind.Int, clr.Big2("op_Addition"));
        Add("Int.sub", a01, Kind.Int, clr.Big2("op_Subtraction"));
        Add("Int.mul", a01, Kind.Int, clr.Big2("op_Multiply"));
        Add("Int.neg", a0, Kind.Int, clr.Big1("op_UnaryNegation"));
        Add("Int.ediv", a01, Kind.Int, clr.Int2("EDiv"));
        Add("Int.emod", a01, Kind.Int, clr.Int2("EMod"));
        Add("Int.tdiv", a01, Kind.Int, clr.Int2("TDiv"));
        Add("Int.tmod", a01, Kind.Int, clr.Int2("TMod"));
        Add("Int.fdiv", a01, Kind.Int, clr.Int2("FDiv"));
        Add("Int.fmod", a01, Kind.Int, clr.Int2("FMod"));
        Add("Int.pow", a01, Kind.Int, clr.Int2("Pow"));
        Add("Int.natAbs", a0, Kind.Nat, clr.Int1("NatAbs"));
        Add("Int.toNat", a0, Kind.Nat, clr.Int1("ToNat"));
        Add("Int.decEq", a01, Kind.Bool, clr.Big2("op_Equality"));
        Add("Int.decLe", a01, Kind.Bool, clr.Big2("op_LessThanOrEqual"));
        Add("Int.decLt", a01, Kind.Bool, clr.Big2("op_LessThan"));

        // String, and printing numbers
        Add("String.append", a01, Kind.String, clr.Static(clr.LeanString, "Append", clr.String, clr.String));
        Add("String.length", a0, Kind.Nat, clr.Static(clr.LeanString, "Length", clr.String));
        Add("String.decEq", a01, Kind.Bool, clr.Static(clr.LeanString, "DecEq", clr.String, clr.String));
        Add("instDecidableEqString", a01, Kind.Bool, clr.Static(clr.LeanString, "DecEq", clr.String, clr.String));
        Add("Nat.repr", a0, Kind.String, clr.Static(clr.LeanNat, "Repr", clr.BigInteger));
        Add("Int.repr", a0, Kind.String, clr.Static(clr.LeanInt, "Repr", clr.BigInteger));

        // UInt8 ... UInt64, Int8 ... Int64. Their operations are the .NET integer operations except where Lean's meaning
        // differs, and LeanFixed holds every one so the difference lives in one place with its reason.
        foreach (FixedWidth f in FixedWidth.All)
        {
            Type ft = clr.Fixed[f.Lean];
            void Fx(string op, int[] args, Kind result, Type? resultClr, params Type[] ps) =>
                t[Name.Parse($"{f.Lean}.{op}")] = new Primitive(Name.Parse($"{f.Lean}.{op}"), args, result,
                    il => il.Emit(OpCodes.Call, clr.Static(clr.LeanFixed, f.Lean + char.ToUpperInvariant(op[0]) + op[1..], ps)), resultClr);
            foreach (string op in new[] { "add", "sub", "mul", "div", "mod", "land", "lor", "xor", "shiftLeft", "shiftRight" })
            {
                Fx(op, a01, Kind.Fixed, ft, ft, ft);
            }
            Fx("neg", a0, Kind.Fixed, ft, ft);
            Fx("complement", a0, Kind.Fixed, ft, ft);
            foreach (string op in new[] { "decEq", "decLt", "decLe" })
            {
                Fx(op, a01, Kind.Bool, null, ft, ft);
            }
            Fx("ofNat", a0, Kind.Fixed, ft, clr.BigInteger);
            if (f.Signed)
            {
                Fx("ofInt", a0, Kind.Fixed, ft, clr.BigInteger);
                Fx("toInt", a0, Kind.Int, null, ft);
                Fx("toNatClampNeg", a0, Kind.Nat, null, ft);
            }
            else
            {
                Fx("toNat", a0, Kind.Nat, null, ft);
            }
            // Conversions between widths wrap, and sign-extend from a signed source: exactly the IL conv opcodes.
            foreach (FixedWidth g in FixedWidth.All.Where(g => g != f))
            {
                string conv = $"{f.Lean}.to{g.Lean}";
                OpCode code = (g.Bits, g.Signed) switch
                {
                    (8, false) => OpCodes.Conv_U1, (16, false) => OpCodes.Conv_U2, (32, false) => OpCodes.Conv_U4, (64, false) => OpCodes.Conv_U8,
                    (8, true) => OpCodes.Conv_I1, (16, true) => OpCodes.Conv_I2, (32, true) => OpCodes.Conv_I4, _ => OpCodes.Conv_I8,
                };
                // A source narrower than 64 bits sits on the stack as an int32; widening an unsigned one to 64 bits
                // must zero-extend it, which conv.u8 does and conv.i8 would not.
                if (code == OpCodes.Conv_I8 && !f.Signed)
                {
                    code = OpCodes.Conv_U8;
                }
                t[Name.Parse(conv)] = new Primitive(Name.Parse(conv), a0, Kind.Fixed, il => il.Emit(code), clr.Fixed[g.Lean]);
            }
        }

        // Bool
        AddIl("Bool.decEq", a01, Kind.Bool, il => il.Emit(OpCodes.Ceq));
        AddIl("instDecidableEqBool", a01, Kind.Bool, il => il.Emit(OpCodes.Ceq));
        return t;
    }
}
