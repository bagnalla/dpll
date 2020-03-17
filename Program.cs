using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using static System.Linq.Enumerable;

public class Sat
{
    // A literal is a negative or positive occurrence of a variable.
    struct Literal
    {
	public bool sign;
	public string ident;
	public override string ToString() {
	    return (sign ? "" : "~") + ident;
	}
    }

    // A clause is a disjunction of literals.
    struct Clause
    {
	public List<Literal> lits;
	public override string ToString() {
	    var s = "(";
	    for (var i = 0; i < lits.Count; ++i) {
		s += lits[i].ToString();
		if (i < lits.Count - 1) {
		    s += " | ";
		}
	    }
	    return s + ")";
	}

	public Clause Copy() {
	    return new Clause() { lits = new List<Literal>(lits) };
	}
    }

    // A CNF formula is a conjunction of clauses.
    class Cnf
    {
	public List<string> vars;
	public List<Clause> clauses;

	public override string ToString() {
	    var s = "";
	    for (var i = 0; i < clauses.Count; ++i) {
		s += clauses[i].ToString();
		if (i < clauses.Count - 1)
		    s += " & ";
	    }
	    return s;
	}

	public override bool Equals(Object o) {
	    var f = o as Cnf;
	    return f is null ? false : clauses.SequenceEqual(f.clauses);
	}

	// whatever
	public override int GetHashCode() { return 0; }

	public Cnf Copy() {
	    return new Cnf() { vars = new List<string>(vars),
			       clauses = clauses.Select(x => x.Copy()).ToList() };
	}
    
	public Cnf CopyWith(Action<List<Clause>> f) {
	    var copy = this.Copy();
	    f(copy.clauses);
	    return copy;
	}
    }

    static Literal lit(bool sign, string ident) {
	return new Literal() { sign = sign, ident = ident };
    }

    static List<T> singleton<T>(T x) {
	return new List<T>(new T[] { x });
    }

    static Clause? parse_dimacs_line(string s) {
	var tokens = s.Split();
	if (tokens.Length == 0 || tokens[0] == "c" || tokens[0] == "p") {
	    return null;
	}
	else {
	    return new Clause() { lits = tokens.Take(tokens.Length - 1).Select(n => {
			var ix = Int32.Parse(n);
			return lit(ix >= 0, "x" + (ix >= 0 ? ix : -ix));
		    }).ToList() };
	}
    }

    static Cnf parse_dimacs(IEnumerable<string> dimacs) {
	return new Cnf() { clauses =
			   dimacs.Select(l => parse_dimacs_line(l))
			   .Where(x => x != null).Cast<Clause>().ToList() };
    }

    static bool eval_clause(Clause c, Dictionary<string, bool> env) {
	return c.lits.Aggregate(false,
				(x, y) => x |
				(y.sign ? env[y.ident] : !env[y.ident]));
    }

    // Evaluate a CNF formula under a given environment.
    static bool eval(Cnf f, Dictionary<string, bool> env) {
	return f.clauses.Aggregate(true, (x, y) => x & eval_clause(y, env));
    }

    // Find all variables that occur in a CNF formula.
    static List<string> fvs(Cnf f) {
	return f.clauses.Select(x => x.lits.Select(y => y.ident))
	    .SelectMany(x => x).Distinct().ToList();
    }

    enum Polarity { Unknown = 0, Negative = 1, Positive = 2, Mixed = 3 };

    static Polarity litPolarity(Literal l) {
	return l.sign ? Polarity.Positive : Polarity.Negative;
    }

    // Determine the polarity of a variable in a CNF clause.
    static Polarity clausePolarity(string x, Clause c) {
	return c.lits.Where(l => l.ident == x)
	    .Aggregate(Polarity.Unknown, (acc, l) => acc | litPolarity(l));
    }

    // Determine the polarity of a variable in a CNF formula.
    static Polarity polarity(string x, Cnf f) {
	var pol = Polarity.Unknown;
	for (var i = 0; i < f.clauses.Count;) {
	    var c_pol = clausePolarity(x, f.clauses[i]);
	    if (c_pol == Polarity.Mixed) {
		f.clauses.RemoveAt(i);
	    }
	    else {
		pol |= c_pol; // combine polarities with bitwise OR
		++i;
	    }
	}
	return pol;
    }

    // Compute polarities for all variables in one linear pass. Assumes
    // no clause contains multiple occurrences of a variable (TODO:
    // pre-process the formula in the very beginning to remove
    // duplicates or detect unsatisfiable clauses).
    static Dictionary<string, Polarity> polarities(Cnf f) {
	var pols = new Dictionary<string, Polarity>();
	foreach (var c in f.clauses) {
	    foreach (var l in c.lits)  {
		pols[l.ident] |= litPolarity(l);
	    }
	}
	return pols;
    }

    // Determine if the variables in the formula are a consistent set
    // (no mixed polarities).
    static bool is_consistent_set(Dictionary<string, Polarity> pols) {
	foreach (var kv in pols) {
	    if (kv.Value != Polarity.Mixed) continue;
	    else return false;
	}
	return true;
    }

    // Return the satisfying assignment for a consistent set.
    static List<Tuple<string, bool>>
	consistent_set(Dictionary<string, Polarity> pols) {
	return pols.Select(kv => Tuple.Create(kv.Key,
					      kv.Value == Polarity.Positive))
	    .ToList();
    }

    // Check for an empty clause.
    static bool is_there_empty_clause(Cnf f) {
	return f.clauses.Any(c => c.lits.Count == 0);
    }

    // Permanently set all occurrences of x to true. Assumes positive
    // polarity at all occurrences.
    static void setTrue(Cnf f, string x) {
	f.vars.Remove(x);
	// Eliminate clauses containing x.
	for (var i = 0; i < f.clauses.Count;) {
	    if (f.clauses[i].lits.Exists(lit => lit.ident == x)) {
		f.clauses.RemoveAt(i);
	    }
	    else ++i;	  
	}
    }

    // Set all occurrences of x to false. Assumes negative polarity at
    // all occurrences. Returns true if the formula becomes
    // unsatisfiable.
    static bool setFalse(Cnf f, string x) {
	f.vars.Remove(x);
	// Eliminate x from clauses.
	for (var i = 0; i < f.clauses.Count;) {
	    f.clauses[i].lits.RemoveAll(lit => lit.ident == x);
	    // If a clause becomes empty then the formula is unsatisfiable.
	    if (f.clauses.Count == 0) { return true; }
	    else ++i;
	}
	return false;
    }

    // Unit propagation.
    static List<Tuple<string, bool>> unit_propagate(Cnf f) {
	var assigns = new List<Tuple<string, bool>>();
	for (var i = 0; i < f.clauses.Count; ++i) {
	    if (f.clauses[i].lits.Count == 1) {
		var lit = f.clauses[i].lits[0];
		if (lit.sign) {
		    assigns.Add(Tuple.Create(lit.ident, true));
		    setTrue(f, lit.ident);
		}
		else {
		    if (setFalse(f, lit.ident)) { return null; }
		    else {
			assigns.Add(Tuple.Create(lit.ident, false));
		    }
		}
	    }
	}
	return assigns;
    }

    static List<Tuple<string, bool>> 
	pure_literal_assign(Cnf f, Dictionary<string, Polarity> pols) {
	var assigns = new List<Tuple<string, bool>>();
	foreach (var kv in pols) {
	    switch (kv.Value) {
		case Polarity.Negative:
		    assigns.Add(Tuple.Create(kv.Key, false));
		    if (setFalse(f, kv.Key)) {
			return null; // unsat
		    }
		    break;
		case Polarity.Positive:
		    assigns.Add(Tuple.Create(kv.Key, true));
		    setTrue(f, kv.Key);
		    break;
	    }
	}
	return null;
    }

    // EFFECT: removes the chosen variable from f.vars.
    static string choose_literal(Cnf f) {
	var x = f.vars[f.vars.Count-1];
	f.vars.RemoveAt(f.vars.Count-1);
	return null;
    }

    // DPLL solver.
    static List<Tuple<string, bool>> DPLL (Cnf f) {
	// First make a copy of the CNF formula to work with.
	f = f.Copy();

	var pols = polarities(f);
	if (is_consistent_set(pols)) {
	    return consistent_set(pols);
	}
	if (is_there_empty_clause(f)) {
	    return null;
	}
	var assigns = unit_propagate(f);
	var assigns2 = pure_literal_assign(f, pols);
	if (assigns2 is null) {
	    return null;
	}
	else {
	    assigns = assigns.Concat(assigns2).ToList();
	}
	if (f.vars.Count == 0) {
	    return assigns;
	}

	// Choose a literal to branch on.
	var l = choose_literal(f);
	
	// First try negative polarity.
	f.clauses.Add(new Clause() { lits = singleton(lit(false, l)) } );
	var assigns3 = DPLL(f);
	// If the result is non null (the formula was satisfiable)
	// then we return the satisfying asignment.
	if (assigns3 != null) {
	    return assigns.Concat(assigns3).ToList();
	}

	// Otherwise (the formula was unsat), try changing the chosen
	// literal to positive polarity.
	f.clauses[f.clauses.Count-1].lits[0] = lit(true, l);
	assigns3 = DPLL(f);

	// If the formula is unsat with both polarities for the chosen
	// literal then it's unsat overall. In that case, we return
	// null. Otherwise we return the satisfying assignment.
	return assigns3 is null ? null : assigns.Concat(assigns3).ToList();
    }

    // Literal elimination. Modifies the CNF formula in place.
    static List<Tuple<string, bool>> litElim(Cnf f) {
	var assigns = new List<Tuple<string, bool>>();
	foreach (var x in f.vars) {
	    var pol = polarity(x, f);
	    switch (pol) {
		case Polarity.Unknown:
		    Console.WriteLine("error: unknown polarity for variable " + x +
				      " (it doesn't occur anywhere in the formula)");
		    break;
		case Polarity.Positive:
		    assigns.Add(Tuple.Create(x, true));
		    setTrue(f, x);
		    break;
		case Polarity.Negative:
		    assigns.Add(Tuple.Create(x, false));
		    if (setFalse(f, x)) return null;
		    break;
		default: break;
	    }
	}
	return assigns;
    }

    public static void Main() {
	var dimacs = File.ReadLines("2.dimacs");
	var f = parse_dimacs(dimacs);

	// var f = new Cnf() {
	//   vars = new List<string>(new string[] { "x", "y", "z" } ),
	//   clauses = new List<Clause>(new Clause[] {
	// 	  new Clause() { lits = new List<Literal>(new Literal[] {
	// 		lit(true, "x"), lit(false, "y"), lit(false, "z") } )
	// 	  } }) };

	Console.WriteLine("Formula: " + f.ToString());
	// var sol = solve(f);
	var sol = DPLL(f);
	if (sol is null) {
	    Console.WriteLine("UNSAT");
	}
	else {
	    Console.WriteLine("SAT:");
	    foreach (var a in sol) {
		Console.WriteLine(a.ToString());
	    }
	}
    }
}
