using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;

namespace LeanToDotNet.Runtime;

/// <summary>Thrown by a compiled recursive function whose thread is about to run out of stack.</summary>
public sealed class LeanStackOverflowException() : Exception("the recursion needs more stack than this thread has");

/// <summary>
/// Deep recursion without crashing the process. A .NET stack overflow cannot be caught: it ends the process. So every
/// compiled recursive method first asks whether a few more frames will fit, and when they will not, throws
/// <see cref="LeanStackOverflowException"/>, which unwinds like any exception. The public method that started the
/// call catches it and runs the same call again on a thread with a 1 GB stack. Running it again is safe because a
/// compiled Lean function has no side effects: the second run computes the same answer the first would have.
/// </summary>
public static class LeanStack
{
    /// <summary>The check at the top of every recursive method: nanoseconds, and nothing happens unless the stack is nearly full.</summary>
    public static void Check()
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
        {
            throw new LeanStackOverflowException();
        }
    }

    /// <summary>Run a static method on a thread with a 1 GB stack and return what it returns.</summary>
    public static object? RunDeep(RuntimeMethodHandle method, object?[] args)
    {
        MethodBase m = MethodBase.GetMethodFromHandle(method)!;
        object? result = null;
        Exception? error = null;
        var t = new Thread(() =>
        {
            try
            {
                result = m.Invoke(null, args);
            }
            catch (TargetInvocationException e)
            {
                error = e.InnerException ?? e;
            }
        }, 1024 * 1024 * 1024);
        t.Start();
        t.Join();
        if (error is LeanStackOverflowException)
        {
            throw new InsufficientExecutionStackException("the recursion is deeper than even a 1 GB stack allows", error);
        }
        if (error is not null)
        {
            ExceptionDispatchInfo.Throw(error);
        }
        return result;
    }
}
