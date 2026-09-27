using System.Reflection;

namespace LeanToDotNet.Runtime;

/// <summary>
/// <c>ToString</c>, <c>Equals</c> and <c>GetHashCode</c> for the classes lean2il makes from Lean structures and
/// inductive types. Every generated class overrides the three with a call here, so a value prints like a C# record,
/// <c>Node { Left = Leaf, Key = 5, Right = Leaf }</c>, and two values are equal when their fields are, as two
/// Lean values are.
/// </summary>
public static class LeanData
{
    private static FieldInfo[] Fields(Type t) => t.GetFields(BindingFlags.Public | BindingFlags.Instance | BindingFlags.DeclaredOnly);

    public static string Show(object value)
    {
        Type t = value.GetType();
        FieldInfo[] fs = Fields(t);
        return fs.Length == 0 ? t.Name : t.Name + " { " + string.Join(", ", fs.Select(f => f.Name + " = " + Format(f.GetValue(value)))) + " }";
    }

    private static string Format(object? v) => v switch
    {
        null => "null",
        string s => "\"" + s + "\"",
        _ => v.ToString() ?? "",
    };

    public static bool Equal(object value, object? other)
    {
        if (ReferenceEquals(value, other))
        {
            return true;
        }
        if (other is null || other.GetType() != value.GetType())
        {
            return false;
        }
        foreach (FieldInfo f in Fields(value.GetType()))
        {
            if (!Equals(f.GetValue(value), f.GetValue(other)))
            {
                return false;
            }
        }
        return true;
    }

    public static int Hash(object value)
    {
        var h = new HashCode();
        h.Add(value.GetType());
        foreach (FieldInfo f in Fields(value.GetType()))
        {
            h.Add(f.GetValue(value));
        }
        return h.ToHashCode();
    }
}
