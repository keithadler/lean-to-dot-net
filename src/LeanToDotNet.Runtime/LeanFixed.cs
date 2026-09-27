using System.Numerics;

namespace LeanToDotNet.Runtime;

/// <summary>
/// Lean's <c>UInt8</c> ... <c>UInt64</c> and <c>Int8</c> ... <c>Int64</c>, with Lean's meaning where it differs from
/// C#'s: arithmetic wraps, dividing by zero gives zero (and the remainder is the dividend), signed division truncates
/// toward zero and <c>MinValue / -1</c> wraps instead of throwing, and a shift count wraps around the width, so
/// <c>1 &lt;&lt;&lt; 65</c> on a <c>UInt64</c> is 2.
/// </summary>
public static class LeanFixed
{
    // UInt8 as byte
    public static byte UInt8Add(byte a, byte b) => unchecked((byte)(a + b));
    public static byte UInt8Sub(byte a, byte b) => unchecked((byte)(a - b));
    public static byte UInt8Mul(byte a, byte b) => unchecked((byte)(a * b));
    public static byte UInt8Neg(byte a) => unchecked((byte)(0 - a));
    public static byte UInt8Land(byte a, byte b) => (byte)(a & b);
    public static byte UInt8Lor(byte a, byte b) => (byte)(a | b);
    public static byte UInt8Xor(byte a, byte b) => (byte)(a ^ b);
    public static byte UInt8Complement(byte a) => unchecked((byte)~a);
    public static bool UInt8DecEq(byte a, byte b) => a == b;
    public static bool UInt8DecLt(byte a, byte b) => a < b;
    public static bool UInt8DecLe(byte a, byte b) => a <= b;
    public static byte UInt8Div(byte a, byte b) => b == 0 ? (byte)0 : (byte)(a / b);
    public static byte UInt8Mod(byte a, byte b) => b == 0 ? a : (byte)(a % b);
    public static byte UInt8ShiftLeft(byte a, byte b) => unchecked((byte)(a << (int)(b % 8)));
    public static byte UInt8ShiftRight(byte a, byte b) => (byte)(a >> (int)(b % 8));
    public static byte UInt8OfNat(BigInteger x) => unchecked((byte)(ulong)(x & ulong.MaxValue));
    public static BigInteger UInt8ToNat(byte a) => a;
    // UInt16 as ushort
    public static ushort UInt16Add(ushort a, ushort b) => unchecked((ushort)(a + b));
    public static ushort UInt16Sub(ushort a, ushort b) => unchecked((ushort)(a - b));
    public static ushort UInt16Mul(ushort a, ushort b) => unchecked((ushort)(a * b));
    public static ushort UInt16Neg(ushort a) => unchecked((ushort)(0 - a));
    public static ushort UInt16Land(ushort a, ushort b) => (ushort)(a & b);
    public static ushort UInt16Lor(ushort a, ushort b) => (ushort)(a | b);
    public static ushort UInt16Xor(ushort a, ushort b) => (ushort)(a ^ b);
    public static ushort UInt16Complement(ushort a) => unchecked((ushort)~a);
    public static bool UInt16DecEq(ushort a, ushort b) => a == b;
    public static bool UInt16DecLt(ushort a, ushort b) => a < b;
    public static bool UInt16DecLe(ushort a, ushort b) => a <= b;
    public static ushort UInt16Div(ushort a, ushort b) => b == 0 ? (ushort)0 : (ushort)(a / b);
    public static ushort UInt16Mod(ushort a, ushort b) => b == 0 ? a : (ushort)(a % b);
    public static ushort UInt16ShiftLeft(ushort a, ushort b) => unchecked((ushort)(a << (int)(b % 16)));
    public static ushort UInt16ShiftRight(ushort a, ushort b) => (ushort)(a >> (int)(b % 16));
    public static ushort UInt16OfNat(BigInteger x) => unchecked((ushort)(ulong)(x & ulong.MaxValue));
    public static BigInteger UInt16ToNat(ushort a) => a;
    // UInt32 as uint
    public static uint UInt32Add(uint a, uint b) => unchecked((uint)(a + b));
    public static uint UInt32Sub(uint a, uint b) => unchecked((uint)(a - b));
    public static uint UInt32Mul(uint a, uint b) => unchecked((uint)(a * b));
    public static uint UInt32Neg(uint a) => unchecked((uint)(0 - a));
    public static uint UInt32Land(uint a, uint b) => (uint)(a & b);
    public static uint UInt32Lor(uint a, uint b) => (uint)(a | b);
    public static uint UInt32Xor(uint a, uint b) => (uint)(a ^ b);
    public static uint UInt32Complement(uint a) => unchecked((uint)~a);
    public static bool UInt32DecEq(uint a, uint b) => a == b;
    public static bool UInt32DecLt(uint a, uint b) => a < b;
    public static bool UInt32DecLe(uint a, uint b) => a <= b;
    public static uint UInt32Div(uint a, uint b) => b == 0 ? (uint)0 : (uint)(a / b);
    public static uint UInt32Mod(uint a, uint b) => b == 0 ? a : (uint)(a % b);
    public static uint UInt32ShiftLeft(uint a, uint b) => unchecked((uint)(a << (int)(b % 32)));
    public static uint UInt32ShiftRight(uint a, uint b) => (uint)(a >> (int)(b % 32));
    public static uint UInt32OfNat(BigInteger x) => unchecked((uint)(ulong)(x & ulong.MaxValue));
    public static BigInteger UInt32ToNat(uint a) => a;
    // UInt64 as ulong
    public static ulong UInt64Add(ulong a, ulong b) => unchecked((ulong)(a + b));
    public static ulong UInt64Sub(ulong a, ulong b) => unchecked((ulong)(a - b));
    public static ulong UInt64Mul(ulong a, ulong b) => unchecked((ulong)(a * b));
    public static ulong UInt64Neg(ulong a) => unchecked((ulong)(0 - a));
    public static ulong UInt64Land(ulong a, ulong b) => (ulong)(a & b);
    public static ulong UInt64Lor(ulong a, ulong b) => (ulong)(a | b);
    public static ulong UInt64Xor(ulong a, ulong b) => (ulong)(a ^ b);
    public static ulong UInt64Complement(ulong a) => unchecked((ulong)~a);
    public static bool UInt64DecEq(ulong a, ulong b) => a == b;
    public static bool UInt64DecLt(ulong a, ulong b) => a < b;
    public static bool UInt64DecLe(ulong a, ulong b) => a <= b;
    public static ulong UInt64Div(ulong a, ulong b) => b == 0 ? (ulong)0 : (ulong)(a / b);
    public static ulong UInt64Mod(ulong a, ulong b) => b == 0 ? a : (ulong)(a % b);
    public static ulong UInt64ShiftLeft(ulong a, ulong b) => unchecked((ulong)(a << (int)(b % 64)));
    public static ulong UInt64ShiftRight(ulong a, ulong b) => (ulong)(a >> (int)(b % 64));
    public static ulong UInt64OfNat(BigInteger x) => unchecked((ulong)(ulong)(x & ulong.MaxValue));
    public static BigInteger UInt64ToNat(ulong a) => a;
    // Int8 as sbyte
    public static sbyte Int8Add(sbyte a, sbyte b) => unchecked((sbyte)(a + b));
    public static sbyte Int8Sub(sbyte a, sbyte b) => unchecked((sbyte)(a - b));
    public static sbyte Int8Mul(sbyte a, sbyte b) => unchecked((sbyte)(a * b));
    public static sbyte Int8Neg(sbyte a) => unchecked((sbyte)(0 - a));
    public static sbyte Int8Land(sbyte a, sbyte b) => (sbyte)(a & b);
    public static sbyte Int8Lor(sbyte a, sbyte b) => (sbyte)(a | b);
    public static sbyte Int8Xor(sbyte a, sbyte b) => (sbyte)(a ^ b);
    public static sbyte Int8Complement(sbyte a) => unchecked((sbyte)~a);
    public static bool Int8DecEq(sbyte a, sbyte b) => a == b;
    public static bool Int8DecLt(sbyte a, sbyte b) => a < b;
    public static bool Int8DecLe(sbyte a, sbyte b) => a <= b;
    public static sbyte Int8Div(sbyte a, sbyte b) => b == 0 ? (sbyte)0 : (b == -1 ? unchecked((sbyte)(0 - a)) : (sbyte)(a / b));
    public static sbyte Int8Mod(sbyte a, sbyte b) => b == 0 ? a : (b == -1 ? (sbyte)0 : (sbyte)(a % b));
    public static sbyte Int8ShiftLeft(sbyte a, sbyte b) => unchecked((sbyte)(a << (int)((byte)b % 8)));
    public static sbyte Int8ShiftRight(sbyte a, sbyte b) => (sbyte)(a >> (int)((byte)b % 8));
    public static sbyte Int8OfInt(BigInteger x) => unchecked((sbyte)(long)(ulong)(x & ulong.MaxValue));
    public static sbyte Int8OfNat(BigInteger x) => Int8OfInt(x);
    public static BigInteger Int8ToInt(sbyte a) => a;
    public static BigInteger Int8ToNatClampNeg(sbyte a) => a < 0 ? BigInteger.Zero : a;
    // Int16 as short
    public static short Int16Add(short a, short b) => unchecked((short)(a + b));
    public static short Int16Sub(short a, short b) => unchecked((short)(a - b));
    public static short Int16Mul(short a, short b) => unchecked((short)(a * b));
    public static short Int16Neg(short a) => unchecked((short)(0 - a));
    public static short Int16Land(short a, short b) => (short)(a & b);
    public static short Int16Lor(short a, short b) => (short)(a | b);
    public static short Int16Xor(short a, short b) => (short)(a ^ b);
    public static short Int16Complement(short a) => unchecked((short)~a);
    public static bool Int16DecEq(short a, short b) => a == b;
    public static bool Int16DecLt(short a, short b) => a < b;
    public static bool Int16DecLe(short a, short b) => a <= b;
    public static short Int16Div(short a, short b) => b == 0 ? (short)0 : (b == -1 ? unchecked((short)(0 - a)) : (short)(a / b));
    public static short Int16Mod(short a, short b) => b == 0 ? a : (b == -1 ? (short)0 : (short)(a % b));
    public static short Int16ShiftLeft(short a, short b) => unchecked((short)(a << (int)((ushort)b % 16)));
    public static short Int16ShiftRight(short a, short b) => (short)(a >> (int)((ushort)b % 16));
    public static short Int16OfInt(BigInteger x) => unchecked((short)(long)(ulong)(x & ulong.MaxValue));
    public static short Int16OfNat(BigInteger x) => Int16OfInt(x);
    public static BigInteger Int16ToInt(short a) => a;
    public static BigInteger Int16ToNatClampNeg(short a) => a < 0 ? BigInteger.Zero : a;
    // Int32 as int
    public static int Int32Add(int a, int b) => unchecked((int)(a + b));
    public static int Int32Sub(int a, int b) => unchecked((int)(a - b));
    public static int Int32Mul(int a, int b) => unchecked((int)(a * b));
    public static int Int32Neg(int a) => unchecked((int)(0 - a));
    public static int Int32Land(int a, int b) => (int)(a & b);
    public static int Int32Lor(int a, int b) => (int)(a | b);
    public static int Int32Xor(int a, int b) => (int)(a ^ b);
    public static int Int32Complement(int a) => unchecked((int)~a);
    public static bool Int32DecEq(int a, int b) => a == b;
    public static bool Int32DecLt(int a, int b) => a < b;
    public static bool Int32DecLe(int a, int b) => a <= b;
    public static int Int32Div(int a, int b) => b == 0 ? (int)0 : (b == -1 ? unchecked((int)(0 - a)) : (int)(a / b));
    public static int Int32Mod(int a, int b) => b == 0 ? a : (b == -1 ? (int)0 : (int)(a % b));
    public static int Int32ShiftLeft(int a, int b) => unchecked((int)(a << (int)((uint)b % 32)));
    public static int Int32ShiftRight(int a, int b) => (int)(a >> (int)((uint)b % 32));
    public static int Int32OfInt(BigInteger x) => unchecked((int)(long)(ulong)(x & ulong.MaxValue));
    public static int Int32OfNat(BigInteger x) => Int32OfInt(x);
    public static BigInteger Int32ToInt(int a) => a;
    public static BigInteger Int32ToNatClampNeg(int a) => a < 0 ? BigInteger.Zero : a;
    // Int64 as long
    public static long Int64Add(long a, long b) => unchecked((long)(a + b));
    public static long Int64Sub(long a, long b) => unchecked((long)(a - b));
    public static long Int64Mul(long a, long b) => unchecked((long)(a * b));
    public static long Int64Neg(long a) => unchecked((long)(0 - a));
    public static long Int64Land(long a, long b) => (long)(a & b);
    public static long Int64Lor(long a, long b) => (long)(a | b);
    public static long Int64Xor(long a, long b) => (long)(a ^ b);
    public static long Int64Complement(long a) => unchecked((long)~a);
    public static bool Int64DecEq(long a, long b) => a == b;
    public static bool Int64DecLt(long a, long b) => a < b;
    public static bool Int64DecLe(long a, long b) => a <= b;
    public static long Int64Div(long a, long b) => b == 0 ? (long)0 : (b == -1 ? unchecked((long)(0 - a)) : (long)(a / b));
    public static long Int64Mod(long a, long b) => b == 0 ? a : (b == -1 ? (long)0 : (long)(a % b));
    public static long Int64ShiftLeft(long a, long b) => unchecked((long)(a << (int)((ulong)b % 64)));
    public static long Int64ShiftRight(long a, long b) => (long)(a >> (int)((ulong)b % 64));
    public static long Int64OfInt(BigInteger x) => unchecked((long)(long)(ulong)(x & ulong.MaxValue));
    public static long Int64OfNat(BigInteger x) => Int64OfInt(x);
    public static BigInteger Int64ToInt(long a) => a;
    public static BigInteger Int64ToNatClampNeg(long a) => a < 0 ? BigInteger.Zero : a;
}
