using Microsoft.VisualStudio.TestTools.UnitTesting;
using Roslyn.Compilers.CSharp;
using RoslynContractCounter;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ContractCounterTests
{
  [TestClass]
  public class ContractUnitTests
  {
    public void CheckContract(string contract, ContractKind kind, Category expected)
    {
      var root = Syntax.ParseExpression(contract);
      var req = new CodeContractCollector(kind, Categories.SemanticCategories);

      req.Visit(root);

      Assert.IsTrue(req.Labels.Count == 1);
      
      var labels = req.Labels[0].Labels.ToList();

      Assert.IsTrue(labels.Count == 1);
      Assert.AreEqual(labels[0], expected.Name);
    }

    public void CheckContractIsOther(string contract, ContractKind kind)
    {
      var root = Syntax.ParseExpression(contract);
      var req = new CodeContractCollector(kind, Categories.SemanticCategories);

      req.Visit(root);

      Assert.IsTrue(req.Labels.Count == 1);
      Assert.IsFalse(req.Labels[0].Labels.Any());
    }

    [TestMethod]
    public void Nullness_contract_tests()
    {
      CheckContract("Contract.Requires(x != null);", ContractKind.Requires, Categories.Nullness);
    }

    [TestMethod]
    public void Parentheses_tests()
    {
      CheckContract("Contract.Requires((x != null));", ContractKind.Requires, Categories.Nullness);
    }

    [TestMethod]
    public void Other_categories_tests()
    {
      CheckContractIsOther("Contract.Requires(x.CustomFunctionCall(y));", ContractKind.Requires);
    }
  }
}
