using System;
using System.Collections.Generic;
using System.Linq;
using Roslyn.Compilers.CSharp;
using System.IO;
using log4net;
using System.Text.RegularExpressions;

namespace RoslynContractCounter
{
  /// <summary>
  /// Generates categorization summaries for all projects in a directory. 
  /// </summary>
  public class Program
  {
    private static readonly ILog Log = LogManager.GetLogger(typeof(Program));

    private const string SummaryFileName = "stats-by-project.csv";
    private const string UncategorizedContractFileName = "uncategorized-contracts.txt";

    /// <summary>
    /// Process all files in the directory passed in, recurse on any directories  
    /// that are found, and process the files they contain.
    /// </summary>
    public static void ProcessDirectory(string targetDirectory, Action<string> processFile)
    {
      // Process the list of files found in the directory. 
      string[] fileEntries = Directory.GetFiles(targetDirectory);
      foreach (string fileName in fileEntries)
      {
        processFile(fileName);
      }

      // Recurse into subdirectories of this directory. 
      string[] subdirectoryEntries = Directory.GetDirectories(targetDirectory);
      foreach (string subdirectory in subdirectoryEntries)
      {
        ProcessDirectory(subdirectory, processFile);
      }
    }

    private static string CategoryLogName(Category category)
    {
      // https://stackoverflow.com/questions/5680730/c-sharp-remove-special-characters
      var clean = Regex.Replace(category.Name, "[^a-zA-Z0-9% ._]", "_");
      return clean + ".txt";
    }

    public struct SubjectProgram
    {
      public string Name { get; set; }
      public string Path { get; set; }
    }

    public static void ShowHelpMessage()
    {
      Console.WriteLine("Usage: RoslynContractCounter <Project Directory> <Output Directory>");
    }

    public static void Main(string[] args)
    {
      if (args.Length != 2)
      {
        ShowHelpMessage();
        return;
      }

      var targetDirectory = args[0];
      var outputDirectory = args[1];

      // Create project records for each of the subdirectories in the target directory.
      var projects = Directory.GetDirectories(targetDirectory);
      var subjects = new List<SubjectProgram>();
      foreach (var path in projects)
      {
        var project = Path.GetFileName(path);
        Log.Info("Added project " + project);
        subjects.Add(new SubjectProgram() { Name = project, Path = path });
      }

      var categories = Categories.SemanticCategories;
      
      // Delete the old category log files
      foreach (var cat in categories)
      {
         var path = Path.Combine(outputDirectory, CategoryLogName(cat));
         if (File.Exists(path))
         {
           File.Delete(path);
         }
      }

      // Aggregate statistic counters
      var agg = new Dictionary<string, int>();
      var reqCnt = 0;
      var ensCnt = 0;
      var invCnt = 0;

      using (var csvStatsByProject = new StreamWriter(Path.Combine(outputDirectory, SummaryFileName)))
      {
        // Write the header.
        csvStatsByProject.WriteLine(string.Join(",", new[] { " " }.Concat(categories.Select(x => x.Name))));

        using (var uncategorizedContractListing = new StreamWriter(Path.Combine(outputDirectory, UncategorizedContractFileName)))
        {
          foreach (var subject in subjects)
          {
            Log.InfoFormat("Computing counts for project {0}.", subject.Name); 

            var req = new CodeContractCollector(ContractKind.Requires, categories);
            var ens = new CodeContractCollector(ContractKind.Ensures, categories);
            var obj = new CodeContractCollector(ContractKind.Invariant, categories);
            var all = new CodeContractCollector(
                      ContractKind.Invariant | ContractKind.Ensures | ContractKind.Requires,
                      categories);

            ProcessDirectory(subject.Path, path =>
            {
              try
              {
                if (path.EndsWith(".cs")) VisitFile(path, new[] { req, ens, obj, all });
                else return;
              }
              catch (Exception ex)
              {
                Log.Warn("Error processing file " + path, ex);
              }
            });

            using (var csv = File.CreateText(Path.Combine(outputDirectory, subject.Name + ".stats")))
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
                agg[cat.Name] = agg[cat.Name] + ens.Labels.Count(t => t.Labels.Contains(cat.Name));

                projRow.Add(all.Labels.Count(t => t.Labels.Contains(cat.Name)).ToString());

                // Dump all the contracts for the category
                using (var log = File.AppendText(Path.Combine(outputDirectory, CategoryLogName(cat))))
                {
                  foreach(var clause in all.Labels.Where(t => t.Labels.Contains(cat.Name)))
                  {
                     log.WriteLine(clause.ContractText);
                  }
                }
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
              agg["Other"] = agg["Other"] + ens.Labels.Count(t => t.Labels.Count == 0);

              csvStatsByProject.WriteLine(string.Join(",", projRow));
            }

            // Print uncatagorized contracts
            foreach (var u in all.Labels.Where(c => c.Labels.Count == 0))
            {
              uncategorizedContractListing.WriteLine(u.ContractText);
              Log.DebugFormat("[Project {0}] No category for contract: {1}", subject.Name, u.ContractText);
            }
          }
        }
      }

      // Dump out aggregate counts
      foreach (var category in agg)
      {
        Console.WriteLine(category.Key + ": " + category.Value);
      }
    }

    /// <summary>
    /// Run the given visitors on the specified file.
    /// </summary>
    public static void VisitFile(string path, SyntaxWalker[] visitors)
    {
      var tree = SyntaxTree.ParseFile(path);
      var root = (CompilationUnitSyntax)tree.GetRoot();

      foreach (var visitor in visitors)
      {
        visitor.Visit(root);
      }
    }
  }
}
