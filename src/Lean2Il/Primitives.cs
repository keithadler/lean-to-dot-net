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
internal sealed record Primitive(Name Name, int[] Args, Kind Result, Action<ILGenerator> Emit);

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

        // Bool
        AddIl("Bool.decEq", a01, Kind.Bool, il => il.Emit(OpCodes.Ceq));
        AddIl("instDecidableEqBool", a01, Kind.Bool, il => il.Emit(OpCodes.Ceq));
        return t;
    }
}
