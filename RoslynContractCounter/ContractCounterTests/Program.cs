using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Roslyn.Compilers;
using Roslyn.Compilers.CSharp;
using Roslyn.Services;
using Roslyn.Services.CSharp;
using System.Diagnostics.Contracts;

namespace ContractCounterTests
{
  static class UtilMethods
  {
    public static bool StaticMethod<T>(IEnumerable<T> arg)
    {
      return true;
    }
  }

  class Program
  {
    public void Collections(string[] elts, string elt, bool indicator)
    {
      Contract.Requires(Contract.ForAll(elts, e => e != null));
      Contract.Requires(elts.Any());
      Contract.Requires(UtilMethods.StaticMethod(elts));
      Contract.Requires(!ReferenceEquals(elts, null));
      Contract.Requires((elts != null));
      Contract.Requires(elt != "");
      Contract.Requires(indicator);
      Contract.Requires(!indicator);
    }
    
    static void Main(string[] args)
    {
    }
  }
}
