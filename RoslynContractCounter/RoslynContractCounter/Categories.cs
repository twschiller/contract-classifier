using Roslyn.Compilers.CSharp;
using System;
using System.Collections.Generic;

namespace RoslynContractCounter
{
  [Flags]
  public enum ContractKind
  {
    None = 0,
    Requires = 1,
    Ensures = Requires << 1,
    Invariant = Ensures << 1,
  }

  /// <summary>
  /// A contract statement with a mutable set of labels/tags.
  /// </summary>
  public class ContractTags
  {
    /// <summary>
    /// Whether the contracts is a requires, ensures, or invariant statement.
    /// </summary>
    public ContractKind ContractType { get; private set; }

    /// <summary>
    /// The source text of the contract.
    /// </summary>
    public string ContractText { get; private set; }

    /// <summary>
    /// The names of the categories which apply to the contract.
    /// </summary>
    public HashSet<string> Labels { get; private set; }

    public ContractTags(ContractKind type, string text)
    {
      this.ContractType = type;
      this.ContractText = text;
      this.Labels = new HashSet<string>();
    }
  }

  /// <summary>
  /// A category of contracts, e.g., "Nullness".
  /// </summary>
  public class Category
  {
    /// <summary>
    /// The name of the category.
    /// </summary>
    public string Name { get; private set; }

    /// <summary>
    /// A predicate that returns <c>true</c> if the contract is in the category given its AST
    /// and contract kind (i.e.., precondition, postcondition, invariant).
    /// </summary>
    public Func<ContractKind, ExpressionSyntax, bool> Rule { get; private set; }

    public Category(string name, Func<ExpressionSyntax, bool> rule)
    {
      this.Name = name;
      this.Rule = (k, e) => rule(e);
    }

    public Category(string name, Func<ContractKind, ExpressionSyntax, bool> rule)
    {
      this.Name = name;
      this.Rule = rule;
    }
  }

  public static class Categories
  {
    public static readonly Category Nullness = new Category("Nullness", CodeContractCollector.IsNullnessCheck);
    public static readonly Category NullOrBlank = new Category("Null/Blank", CodeContractCollector.IsNonNullOrEmptyCheck);
    public static readonly Category NonEmpty = new Category("Non-Empty", c => CodeContractCollector.IsNonEmptyCheck(c) || (CodeContractCollector.IsSizeCheck(c) && CodeContractCollector.IsPositiveCheck(c)));
    public static readonly Category LowerOrUpperBound = new Category("Lower/Upper Bound", c => CodeContractCollector.IsBoundedCheck(c) && !CodeContractCollector.IsSizeCheck(c));
    public static readonly Category Indicator = new Category("Indicator", CodeContractCollector.IsIndicator);
    public static readonly Category FrameCondition = new Category("Frame Condition", CodeContractCollector.IsFrameCondition);
    public static readonly Category ReturnValue = new Category("Return Value", c => CodeContractCollector.IsBoolResult(c) && !CodeContractCollector.IsGetterSetter(c));
    public static readonly Category BoundsCheck = new Category("Bounds Check", CodeContractCollector.IsBoundsCheck);
    public static readonly Category Constant = new Category("Constant", c => CodeContractCollector.IsConstantCheck(c) && !CodeContractCollector.IsSizeCheck(c));
    public static readonly Category Implication = new Category("Implication", c => CodeContractCollector.IsImplication(c));
    public static readonly Category GetterOrSetter = new Category("Getter/Setter", (k, c) => k.HasFlag(ContractKind.Ensures) && CodeContractCollector.IsGetterSetter(c));
    public static readonly Category Membership = new Category("Membership", c => CodeContractCollector.ContainsCheck(c));
    public static readonly Category ExpressionComparison = new Category("Expr. Comparison", c => CodeContractCollector.IsExprComparison(c) || CodeContractCollector.IsComparisonCheck(c));

    /// <summary>
    /// Categories for the ICSE 2014 paper.
    /// </summary>
    public static Category[] SemanticCategories = new Category[]
    {
      Nullness,
      NullOrBlank,
      NonEmpty,
      LowerOrUpperBound,
      Indicator,
      FrameCondition,
      ReturnValue,
      BoundsCheck,
      Constant,
      Implication,
      GetterOrSetter,
      Membership,
      ExpressionComparison,
    };
  }
}
