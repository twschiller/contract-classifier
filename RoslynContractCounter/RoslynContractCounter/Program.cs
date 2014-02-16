using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Roslyn.Compilers;
using Roslyn.Compilers.CSharp;
using Roslyn.Services;
using Roslyn.Services.CSharp;
using System.Diagnostics.Contracts;
using System.IO;

namespace ContractUsage
{

  [Flags]
  public enum ContractKind
  {
    None = 0,
    Requires = 1,
    Ensures = Requires << 1,
    Invariant = Ensures << 1,
  }

  class CodeContractCollector : SyntaxWalker
  {
    /// <summary>
    /// <c>true</c> if membership in one contract category should prevent classification in another category.
    /// Used to allow category ordering to simplify category definition (since later catergories can be more permissive
    /// than normally allowed since a prior category would have picked up the contract).
    /// </summary>
    public static readonly bool CATEGORIES_ARE_MUTEX = true;

    private Dictionary<ContractKind, string> KindStrings = new Dictionary<ContractKind, string>()
        {
            { ContractKind.Requires, "Contract.Requires"},
            { ContractKind.Ensures, "Contract.Ensures"},
            { ContractKind.Invariant, "Contract.Invariant"},
        };

    public class ContractTags
    {
      public ContractKind ContractType { get; private set; }
      public string ContractText { get; private set; }
      public HashSet<string> Labels { get; private set; }

      public ContractTags(ContractKind type, string text)
      {
        this.ContractType = type;
        this.ContractText = text;
        this.Labels = new HashSet<string>();
      }
    }

    public List<ContractTags> Labels { get; private set; }

    private ContractUsage.Program.Category[] Categories;

    public ContractKind ContractType { get; private set; }

    public CodeContractCollector(ContractKind kind, ContractUsage.Program.Category[] categories)
    {
      this.ContractType = kind;
      this.Categories = categories;
      this.Labels = new List<ContractTags>();
    }

    public static bool IsIndicatorMember(string ident)
    {
      if (ident.Equals("Exists")) return true;
      return new string[] { "Is", "Can", "Has" }.Any(prefix => ident.StartsWith(prefix) && ident.Length > prefix.Length && char.IsUpper(ident[prefix.Length]));
    }

    public static bool IsIndicator(ExpressionSyntax expr)
    {
      if (expr is IdentifierNameSyntax)
      {
        // If we just have a lone boolean, consider it to be an indicator variable regardless of the name
        // var ident = ((IdentifierNameSyntax)expr).ToString();
        return true;
      }
      else if (expr is MemberAccessExpressionSyntax)
      {
        // If we just have a lone boolean, consider it to be an indicator variable regardless of the name
        // var ident = ((MemberAccessExpressionSyntax)expr).Name.ToString();
        return true;
      }
      else if (expr is InvocationExpressionSyntax)
      {
        var call = (InvocationExpressionSyntax)expr;

        // Check for instance methods.
        if (call.ArgumentList.Arguments.Count == 0)
        {
          return IsIndicator(call.Expression);
        }
        else if (call.ArgumentList.Arguments.Count == 1)
        {
          if (call.Expression is MemberAccessExpressionSyntax)
          {
            // Check that the member owner appears to be a static class
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
        var b = (BinaryExpressionSyntax)expr;
        return chk(b.Left) && chk(b.Right);
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

        // RHS can be LHS's pre-state as long as it's not an equality.
        return (!IsOldValue(b.Right, b.Left) || expr.Kind != SyntaxKind.EqualsExpression) && containsOld.Any();
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
          Predicate<int> isNull = x =>method.ArgumentList.Arguments[x].ToString().Equals("null");
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
        throw new Exception();
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
        return (bin.Kind == SyntaxKind.NotEqualsExpression) && (bin.Left.ToString().Equals("\"\"") || bin.Right.ToString().Equals("\"\""));
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

    public Func<ContractKind, ExpressionSyntax, bool> UnwrapParens(Func<ContractKind, ExpressionSyntax, bool> predicate)
    {
      return (kind, expr) =>
        {
          if (expr is ParenthesizedExpressionSyntax) return predicate(kind, ((ParenthesizedExpressionSyntax)expr).Expression);
          else return predicate(kind, expr);
        };
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

    public static bool IsBoolResult(ExpressionSyntax expr)
    {
      if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        var b = (BinaryExpressionSyntax)expr;

        if (b.Left is InvocationExpressionSyntax)
        {
          var ie = (InvocationExpressionSyntax)b.Left;
          return ie.Expression.ToString() == "Contract.Result<bool>" || ie.Expression.ToString() == "Contract.Result<int>";
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
      if (expr is InvocationExpressionSyntax)
      {
        return ((InvocationExpressionSyntax)expr).Expression.ToString().Equals("Contract.Result<bool>");
      }
      else if (expr is PrefixUnaryExpressionSyntax && expr.Kind == SyntaxKind.LogicalNotExpression)
      {
        return IsConstantCheck(((PrefixUnaryExpressionSyntax)expr).Operand);
      }
      else if (expr is BinaryExpressionSyntax && expr.Kind == SyntaxKind.EqualsExpression)
      {
        var b = (BinaryExpressionSyntax)expr;
        return b.Right is LiteralExpressionSyntax || b.Left is LiteralExpressionSyntax;
      }
      else
      {
        return false;
      }
    }

    public static bool IsComparisonCheck(ExpressionSyntax expr)
    {
      if (expr.Kind == SyntaxKind.LessThanExpression || expr.Kind == SyntaxKind.LessThanOrEqualExpression)
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

    public override void VisitMethodDeclaration(MethodDeclarationSyntax node)
    {
      base.VisitMethodDeclaration(node);
    }

    /// <summary>
    /// Returns <c>true</c> if the contact is non-sensiscal under behavioral subtyping.
    /// </summary>
    public static bool IsInvalidContract(ExpressionSyntax expr)
    {
      return expr.Kind == SyntaxKind.FalseLiteralExpression;
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
            var contract = node.ArgumentList.Arguments[0];

            var topLevelClauses = new List<ExpressionSyntax>();
            if (contract.Expression.Kind == SyntaxKind.LogicalAndExpression)
            {
              var andEx = (BinaryExpressionSyntax)contract.Expression;
              topLevelClauses.Add(andEx.Left);
              topLevelClauses.Add(andEx.Right);
            }
            else
            {
              topLevelClauses.Add(contract.Expression);
            }

            foreach (var clause in topLevelClauses)
            {
              if (IsInvalidContract(clause)) continue;

              ContractTags tags = new ContractTags(contractKind, clause.ToString());
              foreach (var category in Categories)
              {
                var normalizedRule = UnwrapParens(category.Rule);

                if (normalizedRule(ContractType, clause))
                {
                  tags.Labels.Add(category.Name);

                  if (CATEGORIES_ARE_MUTEX) break;
                }
                else if (CreateEnumerablePredicate(normalizedRule)(ContractType, clause))
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

  class Program
  {
    // Process all files in the directory passed in, recurse on any directories  
    // that are found, and process the files they contain. 
    public static void ProcessDirectory(string targetDirectory, Action<string> processFile)
    {
      // Process the list of files found in the directory. 
      string[] fileEntries = Directory.GetFiles(targetDirectory);
      foreach (string fileName in fileEntries)
        processFile(fileName);

      // Recurse into subdirectories of this directory. 
      string[] subdirectoryEntries = Directory.GetDirectories(targetDirectory);
      foreach (string subdirectory in subdirectoryEntries)
        ProcessDirectory(subdirectory, processFile);
    }

    public class Category
    {
      public string Name { get; private set; }
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

    public class SubjectProgram
    {
      public string Name { get; set; }
      public string Path { get; set; }
    }

    static void Main(string[] args)
    {
      var targetDirectory = args[0];
      var projects = Directory.GetDirectories(targetDirectory);

      var subjects = new List<SubjectProgram>();
      foreach (var path in projects)
      {
        var project = Path.GetFileName(path);
        Console.Write("Added project " + project);
        subjects.Add(new SubjectProgram() { Name = project, Path = path });
      }

      var categories = new Category[]{
                new Category("Nullness", CodeContractCollector.IsNullnessCheck),
                new Category("Null/Blank", CodeContractCollector.IsNonNullOrEmptyCheck),
                new Category("Non-Empty", c => CodeContractCollector.IsNonEmptyCheck(c) || (CodeContractCollector.IsSizeCheck(c) && CodeContractCollector.IsPositiveCheck(c))),
                new Category("Lower/Upper Bound", c => CodeContractCollector.IsBoundedCheck(c) && !CodeContractCollector.IsSizeCheck(c)),
                new Category("Indicator", CodeContractCollector.IsIndicator),
                new Category("Frame Condition", CodeContractCollector.IsFrameCondition),
                new Category("Return Value", c => CodeContractCollector.IsBoolResult(c) && !CodeContractCollector.IsGetterSetter(c)),
                new Category("Bounds Check", CodeContractCollector.IsBoundsCheck),
                new Category("Constant", c => CodeContractCollector.IsConstantCheck(c) && !CodeContractCollector.IsSizeCheck(c)),
                new Category("Implication", c => CodeContractCollector.IsImplication(c)),
                new Category("Getter/Setter", (k,c) => k.HasFlag(ContractKind.Ensures) && CodeContractCollector.IsGetterSetter(c)),
                new Category("State Update", c => CodeContractCollector.IsStateUpdate(c)),
                new Category("Membership", c=> CodeContractCollector.ContainsCheck(c)),
                new Category("Expr. Comparison", c => CodeContractCollector.IsExprComparison(c) || CodeContractCollector.IsComparisonCheck(c)),
                
      };

      var agg = new Dictionary<string, int>();

      var reqCnt = 0;
      var ensCnt = 0;
      var invCnt = 0;

      using (var byProject = new StreamWriter(@"C:\scratch\by-project.csv"))
      {
        // Write the header
        byProject.WriteLine(string.Join(",", new[] { " " }.Concat(categories.Select(x => x.Name))));

        using (var otherLog = new StreamWriter(@"C:\scratch\other-log.txt"))
        {
          foreach (var subject in subjects)
          {
            Console.WriteLine("computing counts for " + subject.Name + "...");

            var req = new CodeContractCollector(ContractKind.Requires, categories);
            var ens = new CodeContractCollector(ContractKind.Ensures, categories);
            var obj = new CodeContractCollector(ContractKind.Invariant, categories);

            var all = new CodeContractCollector(ContractKind.Invariant | ContractKind.Ensures | ContractKind.Requires,
                      categories);


            Action<string> doFile = f =>
            {
              if (f.EndsWith(".cs"))
              {
                try
                {
                  var tree = SyntaxTree.ParseFile(f);
                  var root = (CompilationUnitSyntax)tree.GetRoot();

                  req.Visit(root);
                  ens.Visit(root);
                  obj.Visit(root);
                  all.Visit(root);
                }
                catch (Exception ex)
                {
                  Console.Error.WriteLine(ex.Message);
                }
              }
            };

            ProcessDirectory(subject.Path, doFile);

            using (var csv = File.CreateText(@"C:\scratch\" + subject.Name + ".stats"))
            {
              var projRow = new List<string>();
              projRow.Add(subject.Name);

              foreach (var cat in categories)
              {
                csv.Write(cat.Name + ",");
                csv.Write(req.Labels.Count(t => t.Labels.Contains(cat.Name)) + ",");
                csv.Write(ens.Labels.Count(t => t.Labels.Contains(cat.Name)) + ",");
                csv.Write(obj.Labels.Count(t => t.Labels.Contains(cat.Name)));

                csv.WriteLine();

                if (!agg.ContainsKey(cat.Name)) agg.Add(cat.Name, 0);
                agg[cat.Name] = agg[cat.Name] + all.Labels.Count(t => t.Labels.Contains(cat.Name));

                projRow.Add(all.Labels.Count(t => t.Labels.Contains(cat.Name)).ToString());
              }

              csv.Write("Other" + ",");
              csv.Write(req.Labels.Count(t => t.Labels.Count == 0) + ",");
              csv.Write(ens.Labels.Count(t => t.Labels.Count == 0) + ",");
              csv.Write(obj.Labels.Count(t => t.Labels.Count == 0));
              csv.WriteLine();

              reqCnt += req.Labels.Count;
              ensCnt += ens.Labels.Count;
              invCnt += obj.Labels.Count;

              projRow.Add(all.Labels.Count(t => t.Labels.Count == 0).ToString());

              if (!agg.ContainsKey("Other")) agg.Add("Other", 0);
              agg["Other"] = agg["Other"] + all.Labels.Count(t => t.Labels.Count == 0);

              byProject.WriteLine(string.Join(",", projRow));
            }

            // Print uncatagorized contracts
            foreach (var u in all.Labels.Where(c => c.Labels.Count == 0))
            {
              otherLog.WriteLine(u.ContractText);
              Console.WriteLine(u.ContractText);
            }
          }
        }
      }

      foreach (var entry in agg)
      {
        Console.WriteLine(entry.Key + ": " + entry.Value);
      }
    
    }


  }
}
