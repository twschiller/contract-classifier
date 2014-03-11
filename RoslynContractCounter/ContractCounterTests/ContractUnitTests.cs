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

      Assert.AreEqual(1, req.Labels.Count, "Expected a single top-level contract clause");
      
      var labels = req.Labels[0].Labels.ToList();

      Assert.IsTrue(labels.Count > 0, string.Format("Contract {0} not labeled", contract));
      Assert.AreEqual(1, labels.Count, "Expected a single label for the contract");
      Assert.AreEqual(expected.Name, labels[0], string.Format("Contract {0} miscategorized", contract));
    }

    public void CheckContractIsOther(string contract, ContractKind kind)
    {
      var root = Syntax.ParseExpression(contract);
      var req = new CodeContractCollector(kind, Categories.SemanticCategories);

      req.Visit(root);

      Assert.IsTrue(req.Labels.Count == 1);
      Assert.IsFalse(
        req.Labels[0].Labels.Any(),
        string.Format("Contract '{0}' miscategorized. Label(s): {1}", 
          contract,
          string.Join(",", req.Labels[0].Labels)));
    }

    [TestMethod]
    public void Nullness_contract_tests()
    {
      CheckContract("Contract.Requires(x != null);", ContractKind.Requires, Categories.Nullness);
      CheckContract("Contract.Requires(Contract.ForAll(xs, x => x != null));", ContractKind.Requires, Categories.Nullness);
      CheckContract("Contract.Requires(!ReferenceEquals(elts, null));", ContractKind.Requires, Categories.Nullness);
    }
  
    [TestMethod]
    public void Return_value_tests()
    {
      CheckContract("Contract.Ensures(Contract.Result<bool>() == x > 5);", ContractKind.Ensures, Categories.ReturnValue);
    }
 
    [TestMethod]
    public void Getter_setter_tests()
    {
      // Getters
      CheckContract("Contract.Ensures(Contract.Result<MyObject>() == this.Property);", ContractKind.Ensures, Categories.GetterOrSetter);
      CheckContract("Contract.Ensures(Contract.Result<MyObject>() == Property);", ContractKind.Ensures, Categories.GetterOrSetter);
      CheckContract("Contract.Ensures(Contract.Result<MyObject>().Equals(this.Property));", ContractKind.Ensures, Categories.GetterOrSetter);
      CheckContract("Contract.Ensures(ReferenceEquals(Contract.Result<MyObject>(), this.Property));", ContractKind.Ensures, Categories.GetterOrSetter);
      
      // Setters
      CheckContract("Contract.Ensures(this.Property == arg);", ContractKind.Ensures, Categories.GetterOrSetter);
      CheckContract("Contract.Ensures(Property == arg);", ContractKind.Ensures, Categories.GetterOrSetter);
    }

    [TestMethod]
    public void Frame_condition_tests()
    {
      CheckContract("Contract.Ensures(x == Contract.OldValue(x));", ContractKind.Ensures, Categories.FrameCondition);
      CheckContract("Contract.Ensures(Contract.OldValue(x) == x);", ContractKind.Ensures, Categories.FrameCondition);
    }

    [TestMethod]
    public void Indicator_tests()
    {
      // Parameters
      CheckContract("Contract.Requires(arg.IsOpen);", ContractKind.Requires, Categories.Indicator);
      CheckContract("Contract.Requires(arg.HasFiles);", ContractKind.Requires, Categories.Indicator);
      CheckContract("Contract.Requires(arg.CanRead);", ContractKind.Requires, Categories.Indicator);
      CheckContract("Contract.Requires(arg.FooBar);", ContractKind.Requires, Categories.Indicator);

      // Qualified Properties
      CheckContract("Contract.Requires(this.IsOpen);", ContractKind.Requires, Categories.Indicator);
   
      // Unqualified Properties
      CheckContract("Contract.Requires(IsOpen);", ContractKind.Requires, Categories.Indicator);

      // Lone static methods with a single argument
      CheckContract("Contract.Requires(UtilMethods.StaticMethod(elts));", ContractKind.Requires, Categories.Indicator);
    }

    [TestMethod]
    public void Indicator_with_equality_tests()
    {
      CheckContract("Contract.Requires(arg.IsOpen == true);", ContractKind.Requires, Categories.Indicator);
      CheckContract("Contract.Requires(arg.IsOpen == false);", ContractKind.Requires, Categories.Indicator);
      CheckContract("Contract.Ensures(arg.IsOpen == true);", ContractKind.Ensures, Categories.Indicator);
      CheckContract("Contract.Ensures(arg.IsOpen == false);", ContractKind.Ensures, Categories.Indicator);
    }

    [TestMethod]
    public void Top_level_clause_tests()
    {
      var root = Syntax.ParseExpression("Contract.Requires(x > 5 && y > 1);");
      var req = new CodeContractCollector(ContractKind.Requires, Categories.SemanticCategories);

      req.Visit(root);

      Assert.AreEqual(2, req.Labels.Count(), "Expected categorization for both clauses");

      Assert.AreEqual(1, req.Labels[0].Labels.Count(), "Expected first clause to have a single label");
      Assert.AreEqual(1, req.Labels[1].Labels.Count(), "Expected second clause to have a single label");
    }

    [TestMethod]
    public void Bounds_check_tests()
    {
      CheckContract("Contract.Requires(idx < list.Count);", ContractKind.Requires, Categories.BoundsCheck);
      CheckContract("Contract.Requires(idx < array.Length);", ContractKind.Requires, Categories.BoundsCheck);
    }

    [TestMethod]
    public void Combined_bounds_check()
    {
      CheckContract("Contract.Requires(idx >= 0 && idx < list.Count);", ContractKind.Requires, Categories.BoundsCheck);
    }

    [TestMethod]
    public void Lower_upper_bound_tests()
    {
      CheckContract("Contract.Requires(x > 0);", ContractKind.Requires, Categories.LowerOrUpperBound);
      CheckContract("Contract.Requires(x < 0);", ContractKind.Requires, Categories.LowerOrUpperBound);
      CheckContract("Contract.Requires(x >= 0);", ContractKind.Requires, Categories.LowerOrUpperBound);
      CheckContract("Contract.Requires(x <= 0);", ContractKind.Requires, Categories.LowerOrUpperBound);
    }

    [TestMethod]
    public void State_update_tests()
    {
      CheckContract("Contract.Ensures(x == Contract.OldValue(x) + 1);", ContractKind.Ensures, Categories.StateUpdate);
      CheckContract("Contract.Ensures(x >= Contract.OldValue(x));", ContractKind.Ensures, Categories.StateUpdate);
    }

    [TestMethod]
    public void Null_blank_contract_tests()
    {
      CheckContract("Contract.Requires(string.IsNullOrEmpty(x));", ContractKind.Requires, Categories.NullOrBlank);
      CheckContract("Contract.Requires(string.IsNullOrWhiteSpace(x));", ContractKind.Requires, Categories.NullOrBlank);
      CheckContract("Contract.Requires(str != \"\");", ContractKind.Requires, Categories.NullOrBlank);
    }

    [TestMethod]
    public void Parentheses_tests()
    {
      CheckContract("Contract.Requires((x != null));", ContractKind.Requires, Categories.Nullness);
    }

    [TestMethod]
    public void Non_empty_tests()
    {
      CheckContract("Contract.Requires(collection.Any());", ContractKind.Requires, Categories.NonEmpty);
      CheckContract("Contract.Requires(list.Count > 0);", ContractKind.Requires, Categories.NonEmpty);
      CheckContract("Contract.Requires(array.Length > 0);", ContractKind.Requires, Categories.NonEmpty);
    }

    [TestMethod]
    public void Expression_comparison_tests()
    {
      CheckContract("Contract.Requires(x > y);", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(x.Equals(y));", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(!x.Equals(y));", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(x.Compare(y) < 0);", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(x.Compare(y) <= 0);", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(x.Compare(y) > 0);", ContractKind.Requires, Categories.ExpressionComparison);
      CheckContract("Contract.Requires(x.Compare(y) >= 0);", ContractKind.Requires, Categories.ExpressionComparison);
    }

    [TestMethod]
    public void Other_categories_tests()
    {
      CheckContractIsOther("Contract.Requires(x.CustomFunctionCall(y));", ContractKind.Requires);
      CheckContractIsOther("Contract.Requires(MyClass.CustomFunctionCall(x,y));", ContractKind.Requires);
      
      // Closures are considered to be "other" contracts
      CheckContractIsOther("Contract.Requires(Contract.Forall(xs, x => { return CustomMethod(x) ;} );", ContractKind.Requires); 
    }

    [TestMethod]
    public void Implication_tests()
    {
      CheckContract("Contract.Requires(x > 0 ? y < 0 : true));", ContractKind.Requires, Categories.Implication);
      CheckContract("Contract.Requires(x == null || x.Property);", ContractKind.Requires, Categories.Implication);
    }

    [TestMethod]
    public void Membership_tests()
    {
      CheckContract("Contract.Requires(collection.Contains(arg));", ContractKind.Requires, Categories.Membership);
      CheckContract("Contract.Requires(!collection.Contains(arg));", ContractKind.Requires, Categories.Membership);
      CheckContract("Contract.Requires(dictionary.ContainsKey(arg));", ContractKind.Requires, Categories.Membership);
      CheckContract("Contract.Requires(!dictionary.ContainsKey(arg));", ContractKind.Requires, Categories.Membership);
    }

    [TestMethod]
    public void Constant_tests()
    {
      CheckContract("Contract.Requires(this.Field == 5);", ContractKind.Requires, Categories.Constant);
      CheckContract("Contract.Requires(this.Field == \"Hello World\");", ContractKind.Requires, Categories.Constant);
    }

    [TestMethod]
    public void Invalid_contract_tests()
    {
      var root = Syntax.ParseExpression("Contract.Requires(false);");
      var req = new CodeContractCollector(ContractKind.Requires, Categories.SemanticCategories);

      req.Visit(root);
      
      Assert.AreEqual(0, req.Labels.Count, "Invalid requires contract should be skipped");
    }
  }
}
