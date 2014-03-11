using Roslyn.Compilers.CSharp;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace RoslynContractCounter
{
  /// <summary>
  /// Walks over a C# AST collecting and categorizing contracts.
  /// </summary>
  public class CodeContractCollector : SyntaxWalker
  {
    /// <summary>
    /// <c>true</c> if membership in one contract category should prevent classification in another category.
    /// Used to allow category ordering to simplify category definition (since later catergories can be more permissive
    /// than normally allowed since a prior category would have picked up the contract).
    /// </summary>
    public const bool CATEGORIES_ARE_MUTEX = true;

    private static Dictionary<ContractKind, string> KindStrings = new Dictionary<ContractKind, string>()
        {
            { ContractKind.Requires, "Contract.Requires"},
            { ContractKind.Ensures, "Contract.Ensures"},
            { ContractKind.Invariant, "Contract.Invariant"},
        };

    public List<ContractTags> Labels { get; private set; }

    private Category[] Categories;

    public ContractKind ContractType { get; private set; }

    /// <summary>
    /// Create a <see cref="CodeContractCollector"/> for the given kinds of contracts and categories
    /// </summary>
    /// <param name="kind">The kind(s) of contracts to operate on</param>
    /// <param name="categories">
    /// An ordered array of categories where earlier categories take precedence if
    /// the <see cref="CATEGORIES_ARE_MUTEX"/> flag is set
    /// </param>
    public CodeContractCollector(ContractKind kind, Category[] categories)
    {
      this.ContractType = kind;
      this.Categories = categories;
      this.Labels = new List<ContractTags>();
    }

    public static bool IsIndicator(ExpressionSyntax expr)
    {
      if (expr is IdentifierNameSyntax)
      {
        // If we just have a lone boolean, consider it to be an indicator variable regardless of the name
        return true;
      }
      else if (expr is MemberAccessExpressionSyntax)
      {
        // If we just have a lone boolean, consider it to be an indicator variable regardless of the name
        return true;
      }
      else if (expr is InvocationExpressionSyntax)
      {
        var call = (InvocationExpressionSyntax)expr;

        if (call.ToString().StartsWith("Contract.Result"))
        {
          return false;
        }

        // Check for instance methods.
        if (call.ArgumentList.Arguments.Count == 0)
        {
          return IsIndicator(call.Expression);
        }
        else if (call.ArgumentList.Arguments.Count == 1)
        {
          if (call.Expression is MemberAccessExpressionSyntax)
          {
            // Check that the base member appears to be a static class. 
            // XXX: how can we prevent this from catching too much?
            return char.IsUpper(((MemberAccessExpressionSyntax)call.Expression).Expression.ToString()[0]);
          }
          else
          {
            return false;
          }
        }
        else
        {
          return false;
        }
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        return IsIndicator(((PrefixUnaryExpressionSyntax)expr).Operand);
      }
      else if (expr is BinaryExpressionSyntax && (expr.Kind == SyntaxKind.EqualsExpression || expr.Kind == SyntaxKind.NotEqualsExpression))
      {
        // Support the Indicator == true case
        var b = (BinaryExpressionSyntax)expr;
        
        Predicate<ExpressionSyntax> IsBoolLiteral = e => {
          if (e is LiteralExpressionSyntax){
            return e.ToString() == "true" || e.ToString() == "false";
          }else{
            return false;
          }
        };

        var lhs = IsIndicator(b.Left) && IsBoolLiteral(b.Right);
        var rhs = IsIndicator(b.Right) && IsBoolLiteral(b.Left);

        return lhs || rhs;
      }
      else
      {
        return false;
      }
    }

    public static bool IsContractResult(ExpressionSyntax expr)
    {
      return expr is InvocationExpressionSyntax && ((InvocationExpressionSyntax)expr).Expression.ToString().StartsWith("Contract.Result<");
    }

    public static bool IsGetterSetter(ExpressionSyntax expr)
    {
      Predicate<ExpressionSyntax> chk = e => e is MemberAccessExpressionSyntax || e is IdentifierNameSyntax ||
          IsContractResult(e) || e.Kind == SyntaxKind.ThisExpression;

      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        Func<ExpressionSyntax, ExpressionSyntax, bool> result = (lhs, rhs) =>
        {
          var lhsOk = chk(lhs);
          var rhsOk = rhs is IdentifierNameSyntax || rhs is MemberAccessExpressionSyntax || rhs is LiteralExpressionSyntax;
          var constantReturn = IsContractResult(lhs) && rhs is LiteralExpressionSyntax;
          return lhsOk && rhsOk && !constantReturn;
        };

        var b = (BinaryExpressionSyntax)expr;
        return result(b.Left, b.Right) || result(b.Right, b.Left);
      }
      else if (expr is InvocationExpressionSyntax)
      {
        var i = (InvocationExpressionSyntax)expr;

        // Handle ReferenceEquals(Contract.Result<>, x) case
        if (i.Expression.ToString().Equals("ReferenceEquals"))
        {
          return IsContractResult(i.ArgumentList.Arguments[0].Expression) || IsContractResult(i.ArgumentList.Arguments[1].Expression);
        }

        if (i.Expression is MemberAccessExpressionSyntax)
        {
          var m = (MemberAccessExpressionSyntax)i.Expression;
          return m.Name.ToString().Equals("Equals") && chk(m.Expression) && chk(i.ArgumentList.Arguments[0].Expression);
        }

        return false;
      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <c>true</c> if <paramref name="oldValue"/> is the pre-state expression for <paramref name="expr"/>.
    /// </summary>
    public static bool IsOldValue(ExpressionSyntax oldValue, ExpressionSyntax expr)
    {
      if (oldValue is InvocationExpressionSyntax)
      {
        var i = (InvocationExpressionSyntax)oldValue;
        return i.Expression.ToString().Equals("Contract.OldValue") && i.ArgumentList.Arguments[0].Expression.IsEquivalentTo(expr);
      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <tt>true</tt> iff <paramref name="expr"/> relates an expression to its pre-state.
    /// </summary>
    public static bool IsStateUpdate(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax)
      {
        var b = (BinaryExpressionSyntax)expr;

        var containsOld = from e in b.Right.DescendantNodes().OfType<ExpressionSyntax>()
                          where IsOldValue(e, b.Left)
                          select e;
        var oldMatch = containsOld.ToList();
        
        if (IsOldValue(b.Right, b.Left))
        {
          oldMatch.Add(b.Right);
        }

        // RHS can be LHS's pre-state as long as it's not an equality.
        return (!IsOldValue(b.Right, b.Left) || expr.Kind != SyntaxKind.EqualsExpression) && oldMatch.Any();
      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <tt>true</tt> iff <paramref name="expr"/> states that an expression has not been modified.
    /// </summary>
    public static bool IsFrameCondition(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        var b = (BinaryExpressionSyntax)expr;
        return IsOldValue(b.Left, b.Right) || IsOldValue(b.Right, b.Left);
      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <tt>true</tt> iff <paramref name="expr"/> is a binary expression over two non-literals.
    /// </summary>
    public static bool IsExprComparison(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind != SyntaxKind.LogicalAndExpression)
      {
        var b = (BinaryExpressionSyntax)expr;
        return !(IsFrameCondition(expr) || IsStateUpdate(expr) || IsImplication(expr)) &&
               !(b.Right is LiteralExpressionSyntax || b.Left is LiteralExpressionSyntax);
      }
      else if (expr is InvocationExpressionSyntax)
      {
        var m = (InvocationExpressionSyntax)expr;

        if (SimpleMethodName(m) == "Equals" || SimpleMethodName(m) == "ReferenceEquals")
        {
          return !(m.Expression is LiteralExpressionSyntax || m.ArgumentList.Arguments[0].Expression is LiteralExpressionSyntax);
        }
        return false;
      }
      else
      {
        return false;
      }
    }

    public static bool IsNonEmptyCheck(ExpressionSyntax expr)
    {
      if (expr is InvocationExpressionSyntax)
      {
        var i = (InvocationExpressionSyntax)expr;
        if (i.Expression is MemberAccessExpressionSyntax)
        {
          var m = (MemberAccessExpressionSyntax)i.Expression;
          return m.Name.ToString().Equals("Any");
        }

        return false;
      }
      else
      {
        return false;
      }
    }

    public static bool IsSizeCheck(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax)
      {
        var b = (BinaryExpressionSyntax)expr;
        return IsCollectionSizeExpr(b.Left) || IsCollectionSizeExpr(b.Right);
      }
      else
      {
        return false;
      }
    }

    public static bool IsGreaterThanCheck(ExpressionSyntax expr, int val, bool strict)
    {
      var gtKind = strict ? SyntaxKind.GreaterThanExpression : SyntaxKind.GreaterThanOrEqualExpression;
      var ltKind = strict ? SyntaxKind.LessThanExpression : SyntaxKind.LessThanOrEqualExpression;


      if (expr is BinaryExpressionSyntax)
      {
        var b = (BinaryExpressionSyntax)expr;

        if (b.Kind == gtKind)
        {
          return b.Right.ToString().Equals(val.ToString());
        }
        else if (b.Kind == ltKind)
        {
          return b.Left.ToString().Equals(val.ToString());
        }
        else
        {
          return false;
        }
      }
      else
      {
        return false;
      }
    }


    public static bool IsBoundedCheck(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax)
      {
        var b = (BinaryExpressionSyntax)expr;

        Predicate<ExpressionSyntax> isRegular = e => !(e is InvocationExpressionSyntax) || IsContractResult(e);

        switch (expr.Kind)
        {
          case SyntaxKind.GreaterThanOrEqualExpression:
          case SyntaxKind.GreaterThanExpression:
          case SyntaxKind.LessThanExpression:
          case SyntaxKind.LessThanOrEqualExpression:
            return (b.Left is LiteralExpressionSyntax || b.Right is LiteralExpressionSyntax) &&
                   (isRegular(b.Left) && isRegular(b.Right));

          default:
            return false;
        }
      }
      else
      {
        return false;
      }
    }

    public static bool IsPositiveCheck(ExpressionSyntax expr)
    {
      return IsGreaterThanCheck(expr, 0, true) || IsGreaterThanCheck(expr, 1, false);
    }

    public static bool IsCollectionSizeExpr(ExpressionSyntax expr)
    {
      if (expr is MemberAccessExpressionSyntax)
      {
        // Check for Count, Length, VertexCount (from QuickGraph)
        var mae = (MemberAccessExpressionSyntax)expr;
        return new string[] { "Count", "Length", "VertexCount" }.Any(m => mae.Name.ToString().Equals(m));

      }
      else if (expr is InvocationExpressionSyntax)
      {
        // Check for .GetLength(...)
        return SimpleMethodName(((InvocationExpressionSyntax)expr)).Equals("GetLength");
      }
      else
      {
        return false;
      }
    }

    public static bool IsBoundsCheck(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.LessThanExpression)
      {
        var b = (BinaryExpressionSyntax)expr;
        return IsCollectionSizeExpr(b.Right);
      }
      else if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalAndExpression)
      {
        // XXX This is dead code because the top-level conjuncts are split

        var b = (BinaryExpressionSyntax)expr;
        return IsGreaterThanCheck(b.Left, 0, false) && IsBoundsCheck(b.Right);
      }
      else
      {
        return false;
      }
    }

    public static bool IsNullnessCheck(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.NotEqualsExpression)
      {
        var cond = (BinaryExpressionSyntax)expr;
        return cond.Left.Kind == SyntaxKind.NullLiteralExpression || cond.Right.Kind == SyntaxKind.NullLiteralExpression;
      }
      else if (expr is InvocationExpressionSyntax)
      {
        // include special expressions from the subject programs
        var helperMethods = new string[]
        {
          "EnumerableContract.ElementsNotNull",
          "cce.NonNull",
          "cce.NonNullElements",
          "cce.NonNullDictionaryAndValues",
        };

        return helperMethods.Any(m => ((InvocationExpressionSyntax)expr).Expression.ToString().Equals(m));
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        // Check for !ReferenceEquals

        var inner = ((PrefixUnaryExpressionSyntax)expr).Operand;
        if (inner is InvocationExpressionSyntax)
        {
          var method = (InvocationExpressionSyntax)inner;
          Predicate<int> isNull = x => method.ArgumentList.Arguments[x].ToString().Equals("null");
          return SimpleMethodName(method).Equals("ReferenceEquals") && (isNull(0) || isNull(1));
        }
        return false;
      }
      else
      {
        return false;
      }
    }

    public static string SimpleMethodName(InvocationExpressionSyntax expr)
    {
      if (expr.Expression is IdentifierNameSyntax)
      {
        return expr.Expression.ToString();
      }
      else if (expr.Expression is MemberAccessExpressionSyntax)
      {
        return ((MemberAccessExpressionSyntax)expr.Expression).Name.ToString();
      }
      else if (expr.Expression is GenericNameSyntax)
      {
        return expr.Expression.ToString();
      }
      else
      {
        throw new Exception(string.Format("Unexpected method invocation node: {0}", expr.ToString()));
      }
    }

    public static bool ContainsCheck(ExpressionSyntax expr)
    {
      if (expr is InvocationExpressionSyntax)
      {
        var i = (InvocationExpressionSyntax)expr;

        if (i.ArgumentList.Arguments.Count == 1)
        {
          // include some special methods from QuickGraph
          return new string[] { "Contains", "ContainsVertex", "ContainsEdge", "ContainsKey" }.Any(n => n.Equals(SimpleMethodName(i)));
        }
        else
        {
          return false;
        }
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        return ContainsCheck(((PrefixUnaryExpressionSyntax)expr).Operand);
      }
      else
      {
        return false;
      }
    }

    public static bool IsNonNullOrEmptyCheck(ExpressionSyntax expr)
    {
      if (expr is InvocationExpressionSyntax)
      {
        var method = ((InvocationExpressionSyntax)expr).Expression;
        return method.ToString().Equals("string.IsNullOrEmpty") ||
               method.ToString().Equals("string.IsNullOrWhiteSpace") ||
               method.ToString().Equals("String.IsNullOrEmpty") ||
               method.ToString().Equals("String.IsNullOrWhiteSpace");

      }
      else if (expr is BinaryExpressionSyntax)
      {
        var bin = (BinaryExpressionSyntax)expr;

        // Check for str != ""
        if ((bin.Kind == SyntaxKind.NotEqualsExpression) && (bin.Left.ToString().Equals("\"\"") || bin.Right.ToString().Equals("\"\"")))
        {
          return true;
        }

        // Check for string.IsNullOrEmpty == false
        if (bin.Kind == SyntaxKind.EqualsExpression || bin.Kind == SyntaxKind.NotEqualsExpression)
        {
          Func<ExpressionSyntax, ExpressionSyntax, bool> isCheck = (lhs, rhs) =>
          {
            return lhs is InvocationExpressionSyntax && IsNonNullOrEmptyCheck(lhs) && rhs is LiteralExpressionSyntax;
          };

          return isCheck(bin.Left, bin.Right) || isCheck(bin.Right, bin.Left);
        }

        return false;
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        return IsNonNullOrEmptyCheck(((PrefixUnaryExpressionSyntax)expr).Operand);
      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <tt>true</tt> if <paramref name="expr"/> encodes an implication; currently that the expression
    /// is logical-or expression.
    /// </summary>
    public static bool IsImplication(ExpressionSyntax expr)
    {
      if (expr is ConditionalExpressionSyntax) return true; // Ternary operator.
      else return expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalOrExpression;
    }

    /// <summary>
    /// Returns a predicate that detects <paramref name="predicate"/> in <tt>Enumerable.All</tt> and <tt>Contract.ForAll</tt> methods.
    /// </summary>
    public Func<ContractKind, ExpressionSyntax, bool> CreateEnumerablePredicate(Func<ContractKind, ExpressionSyntax, bool> predicate)
    {
      return (kind, expr) =>
      {
        if (expr is InvocationExpressionSyntax)
        {
          var i = (InvocationExpressionSyntax)expr;

          if (new[] { "Enumerable.All", "Contract.ForAll" }.Any(n => n.Equals(i.Expression.ToString())))
          {
            var d = i.ArgumentList.Arguments[1].Expression;
            if (d is SimpleLambdaExpressionSyntax)
            {
              var l = (SimpleLambdaExpressionSyntax)d;
              return l.Body is ExpressionSyntax && predicate(kind, (ExpressionSyntax)l.Body);
            }

            return false;
          }
        }
        return false;
      };
    }

    public static bool IsResultDefinition(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        var b = (BinaryExpressionSyntax)expr;

        if (b.Left is InvocationExpressionSyntax)
        {
          var ie = (InvocationExpressionSyntax)b.Left;

          var rule = new Regex("^Contract.Result<.*?>()$");
          return rule.IsMatch(ie.Expression.ToString().Trim());
        }
        else
        {
          return false;
        }
      }
      else
      {
        return false;
      }
    }

    public static bool IsConstantCheck(ExpressionSyntax expr)
    {
   
      if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        return IsConstantCheck(((PrefixUnaryExpressionSyntax)expr).Operand);
      }
      else if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        var b = (BinaryExpressionSyntax)expr;

        Func<ExpressionSyntax, ExpressionSyntax, bool> chk = (lhs, rhs) =>
        {
          var simpleExpr = lhs is IdentifierNameSyntax || lhs is MemberAccessExpressionSyntax;
          var otherLiteral = rhs is LiteralExpressionSyntax;
          return simpleExpr && otherLiteral;
        };

        return chk(b.Left, b.Right) || chk(b.Right, b.Left);
      }
      else
      {
        return false;
      }
    }

    public static bool IsComparisonCheck(ExpressionSyntax expr)
    {
      if (expr.Kind == SyntaxKind.LessThanExpression || expr.Kind == SyntaxKind.LessThanOrEqualExpression ||
          expr.Kind == SyntaxKind.GreaterThanExpression || expr.Kind == SyntaxKind.GreaterThanOrEqualExpression)
      {
        var b = (BinaryExpressionSyntax)expr;
        return b.Left is InvocationExpressionSyntax && (SimpleMethodName((InvocationExpressionSyntax)b.Left).Equals("Compare"))
               && b.Right is LiteralExpressionSyntax;
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        var n = (PrefixUnaryExpressionSyntax)expr;

        return n.Operand is InvocationExpressionSyntax && (SimpleMethodName((InvocationExpressionSyntax)n.Operand).Equals("Equals"));

      }
      else
      {
        return false;
      }
    }

    /// <summary>
    /// Returns <c>true</c> if the contact is non-sensiscal under behavioral subtyping.
    /// </summary>
    public static bool IsInvalidContract(ExpressionSyntax expr)
    {
      return expr.Kind == SyntaxKind.FalseLiteralExpression;
    }

    private static IEnumerable<ExpressionSyntax> TopLevelClauses(ExpressionSyntax expr, bool unrollEnumerables)
    {
      var normalized = StripParenthesis(expr);

      var result = new List<ExpressionSyntax>();
  
      if (unrollEnumerables && normalized is InvocationExpressionSyntax)
      {
        var call = (InvocationExpressionSyntax)expr;

        if (new[] { "Enumerable.All", "Contract.ForAll" }.Any(n => n.Equals(call.Expression.ToString())))
        {
          var d = call.ArgumentList.Arguments[1].Expression;
          if (d is SimpleLambdaExpressionSyntax)
          {
            var l = (SimpleLambdaExpressionSyntax)d;

            if (l.Body is ExpressionSyntax)
            {
              return TopLevelClauses(((ExpressionSyntax)l.Body), false);
            }
            else
            {
              // Let this contract be categorized at "Other"
              result.Add(normalized);
              return result;
            }
          }
        }
        else
        {
          // Let this contract be categorized at "Other"
          result.Add(normalized);
          return result;
        }
      }

      if (normalized.Kind == SyntaxKind.LogicalAndExpression)
      {
        var andEx = (BinaryExpressionSyntax)normalized;
        result.AddRange(TopLevelClauses(StripParenthesis(andEx.Left), unrollEnumerables));
        result.AddRange(TopLevelClauses(StripParenthesis(andEx.Right), unrollEnumerables));
      }
      else
      {
        result.Add(normalized);
      }
      return result;
    }

    private static ExpressionSyntax StripParenthesis(ExpressionSyntax expr)
    {
      if (expr is ParenthesizedExpressionSyntax)
      {
        return StripParenthesis(((ParenthesizedExpressionSyntax)expr).Expression);
      }
      else
      {
        return expr;
      }
    }

    public override void VisitInvocationExpression(InvocationExpressionSyntax node)
    {
      if (node.Expression is MemberAccessExpressionSyntax)
      {
        var expr = (MemberAccessExpressionSyntax)node.Expression;

        foreach (var contractKind in KindStrings.Keys)
        {
          if (ContractType.HasFlag(contractKind) && expr.ToString().StartsWith(KindStrings[contractKind]))
          {
            var contract = StripParenthesis(node.ArgumentList.Arguments[0].Expression);
            var topLevelClauses = TopLevelClauses(contract, true);
           
            foreach (var clause in topLevelClauses)
            {
              if (IsInvalidContract(clause)) continue;

              ContractTags tags = new ContractTags(contractKind, clause.ToString());
              foreach (var category in Categories)
              {
                var normalized = StripParenthesis(clause);

                if (category.Rule(ContractType, normalized))
                {
                  tags.Labels.Add(category.Name);

                  if (CATEGORIES_ARE_MUTEX) break;
                }
                else if (CreateEnumerablePredicate(category.Rule)(ContractType, normalized))
                {
                  tags.Labels.Add(category.Name);

                  if (CATEGORIES_ARE_MUTEX) break;
                }
              }
              Labels.Add(tags);
            }
          }
        }
      }
    }
  }
}
