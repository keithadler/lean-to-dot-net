using System.Globalization;
using System.Reflection;

namespace LeanToDotNet;

/// <summary>
/// A generic runtime type instantiated at a type the assembly being written defines: <c>LeanList&lt;Tree&gt;</c>,
/// where <c>LeanList`1</c> comes from the reference assemblies and <c>Tree</c> is a <see cref="System.Reflection.Emit.TypeBuilder"/>.
///
/// <see cref="MetadataLoadContext"/> refuses to build that instantiation, because <c>Tree</c> is not one of its
/// types. But all <c>PersistedAssemblyBuilder</c> needs from it is what goes in the signature: that it is a
/// constructed generic type, its definition, and its arguments. This answers exactly those questions and delegates
/// the rest to the definition. Compiled code never calls a member through it (it goes through the non-generic
/// <c>ILeanList</c> and <c>ILeanOption</c>), so nothing else is asked of it.
/// </summary>
internal sealed class GenericInst(Type definition, Type[] arguments) : TypeDelegator(definition)
{
    private readonly Type _definition = definition;
    private readonly Type[] _arguments = arguments;

    public override bool IsGenericType => true;
    public override bool IsGenericTypeDefinition => false;
    public override bool IsConstructedGenericType => true;
    public override bool ContainsGenericParameters => false;
    public override Type GetGenericTypeDefinition() => _definition;
    public override Type[] GetGenericArguments() => (Type[])_arguments.Clone();
    public override Type[] GenericTypeArguments => (Type[])_arguments.Clone();
    public override Type UnderlyingSystemType => this;
    public override string Name => _definition.Name;
    public override string? FullName => null;
    public override string? AssemblyQualifiedName => null;
    public override string ToString() => _definition.Name.Split('`')[0] + "<" + string.Join(", ", _arguments.Select(a => a.Name)) + ">";
    public override bool Equals(Type? o) => o is GenericInst g && g._definition == _definition && g._arguments.SequenceEqual(_arguments);
    public override bool Equals(object? o) => o is Type t && Equals(t);
    public override int GetHashCode() => HashCode.Combine(_definition, _arguments.Aggregate(0, (h, a) => HashCode.Combine(h, a)));
    protected override bool IsValueTypeImpl() => false;
    protected override bool IsArrayImpl() => false;
    protected override bool IsByRefImpl() => false;
    protected override bool IsPointerImpl() => false;
    protected override bool IsPrimitiveImpl() => false;
    protected override TypeAttributes GetAttributeFlagsImpl() => _definition.Attributes;
    public override Type MakeArrayType() => throw new NotSupportedException();
    public override Type? BaseType => _definition.BaseType;
    public override Assembly Assembly => _definition.Assembly;
    public override Module Module => _definition.Module;
    public override string? Namespace => _definition.Namespace;
    public override Type? DeclaringType => null;

    /// <summary>An instantiation <c>definition&lt;argument&gt;</c>, through the loader when it can and through this when it cannot.</summary>
    public static Type Of(Type definition, Type argument) =>
        argument is System.Reflection.Emit.TypeBuilder or System.Reflection.Emit.EnumBuilder or GenericInst
            || (argument.IsConstructedGenericType && argument.GetGenericArguments().Any(a => a is System.Reflection.Emit.TypeBuilder or GenericInst))
            ? new GenericInst(definition, [argument])
            : definition.MakeGenericType(argument);
}
