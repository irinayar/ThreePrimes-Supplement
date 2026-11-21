using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// VERSION M2 (m = k, m*delta >= 1; article v6, Q65 + Q63). Candidate Q63: Theorem 3.1 holds for every exponent vector a (D = prod p^(a_p^2)).
// For delta = 1/k, m = k (m*delta >= 1), h = ceil(log2 m): compare the exponent log2 D + M of the forced vector a_p(delta) with the best vector
// found by exhaustive search over 0 <= a_p <= a_p(delta)+3 (the search ranks vectors with decimal doubles).
// EXACT part: for every vector reported (forced and best) the counting condition h*d <= M is checked with exact integers
// (d = number of retained coordinates (p,n), n > a_p, p^(n^2) <= D 2^M m with m = 2^h the worst case), and for small cases the
// end-to-end pigeonhole on multiples of D is run with exact integers and the result P_S(Dt) < delta is checked.
// Lean: explicit_upper_B (ThreePrimesTheoremB.lean) states the theorem for an arbitrary a; this program checks finite instances only.
class P {
  static int Ceil2(BigInteger v) { int h = 0; while ((BigInteger.One << h) < v) h++; return h; }
  static int Forced(int p, BigInteger k) { int a = 0; while (BigInteger.Pow(p, 2 * a + 1) <= k) a++; return a; }
  static long CountN(int p, int a, BigInteger lim) { long n = a; while (BigInteger.Pow(p, (int)((n + 1) * (n + 1))) <= lim) n++; return n - a; }
  static long MOf(int[] ps, int[] a, int h, double A, out double Delta) {
    double alpha = a.Sum(); Delta = 0;
    for (int i = 0; i < ps.Length; i++) Delta += (double)a[i] * a[i] * Math.Log(ps[i], 2);
    double Q = (double)h * h * A * A - 4 * (h * alpha - Delta - h);
    double t = (h * A + Math.Sqrt(Math.Max(Q, 0))) / 2;
    return Math.Max(0, (long)Math.Ceiling(t * t - h - Delta));
  }
  static bool ExactCount(int[] ps, int[] a, int h, long M, out long d) {
    BigInteger D = 1; for (int i = 0; i < ps.Length; i++) D *= BigInteger.Pow(ps[i], a[i] * a[i]);
    BigInteger lim = D * (BigInteger.One << (int)M) * (BigInteger.One << h);
    d = 0; for (int i = 0; i < ps.Length; i++) d += CountN(ps[i], a[i], lim);
    return (long)h * d <= M;
  }
  static void Main() {
    var sets = new List<int[]>{ new[]{2}, new[]{3}, new[]{2,3}, new[]{2,5}, new[]{3,5}, new[]{2,3,5}, new[]{2,3,7}, new[]{2,3,5,7} };
    int[] ks = {2,3,5,10,20,50,80,100,200,500,1000,2000,5000,100000,1000000};
    Console.WriteLine("== Part 1: forced vs best exponent vector, delta=1/k; E = log2 D + M (bits). exact check of h*d <= M for both vectors");
    int rows = 0, bad = 0, zero = 0, notAbove = 0; double maxGain = 0, maxRel = 0;
    var best22 = new Dictionary<string, string>();
    foreach (var ps in sets) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      Console.WriteLine("S={" + string.Join(",", ps) + "}");
      foreach (int k in ks) {
        BigInteger kb = k; int h = Ceil2(kb);
        var af = ps.Select(p => Forced(p, kb)).ToArray();
        long Mf = MOf(ps, af, h, A, out double Df); double ef = Df + Mf;
        bool okF = ExactCount(ps, af, h, Mf, out long df);
        int[] best = null; double eb = double.MaxValue; long Mb = 0; var cur = new int[ps.Length];
        void Rec(int i) {
          if (i == ps.Length) { long M = MOf(ps, cur, h, A, out double Dl); double e = Dl + M; if (e < eb - 1e-9) { eb = e; best = (int[])cur.Clone(); Mb = M; } return; }
          for (int a = 0; a <= af[i] + 3; a++) { cur[i] = a; Rec(i + 1); }
        }
        Rec(0);
        bool okB = ExactCount(ps, best, h, Mb, out long db);
        rows++; if (!okF || !okB) bad++;
        double gain = ef - eb; if (gain < 1e-9) zero++; maxGain = Math.Max(maxGain, gain); maxRel = Math.Max(maxRel, gain / ef);
        for (int i = 0; i < ps.Length; i++) if (best[i] < af[i]) { notAbove++; break; }
        Console.WriteLine($"  k={k,8} h={h,3} forced a=[{string.Join(",", af)}] E={ef,9:F2} (exact h*d={h * df}<=M={Mf}: {okF})  best a=[{string.Join(",", best)}] E={eb,9:F2} (exact h*d={h * db}<=M={Mb}: {okB})  gain={gain:F2} rel={gain / ef:F4}");
      }
    }
    Console.WriteLine($"Summary: rows={rows}, exact-count failures={bad}, rows with zero gain={zero}, rows where best has a coordinate below the forced one={notAbove}, max gain={maxGain:F2} bits, max relative gain={maxRel:F4}");
    Console.WriteLine("== Part 2: end-to-end pigeonhole on multiples of D with the BEST (non-forced) vector, exact integers, small cases (M <= 24)");
    foreach (var (ps, k) in new[]{ (new[]{2}, 4), (new[]{2}, 8), (new[]{3}, 2), (new[]{3,5}, 2), (new[]{2,3}, 2), (new[]{2,3}, 3), (new[]{2,5}, 2), (new[]{2,3,5}, 2) }) {
      double A = ps.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2)));
      BigInteger kb = k; int m = k; int h = Ceil2(m);
      var af = ps.Select(p => Forced(p, kb)).ToArray();
      int[] best = null; double eb = double.MaxValue; long Mb = 0; var cur = new int[ps.Length];
      void Rec(int i) {
        if (i == ps.Length) { long M = MOf(ps, cur, h, A, out double Dl); double e = Dl + M; if (e < eb - 1e-9) { eb = e; best = (int[])cur.Clone(); Mb = M; } return; }
        for (int a = 0; a <= af[i] + 3; a++) { cur[i] = a; Rec(i + 1); }
      }
      Rec(0);
      BigInteger D = 1; for (int i = 0; i < ps.Length; i++) D *= BigInteger.Pow(ps[i], best[i] * best[i]);
      if (Mb > 24) { Console.WriteLine($"skip S={{{string.Join(",", ps)}}} k={k}: M={Mb}"); continue; }
      long N0 = 1L << (int)Mb; BigInteger Kmax = D * N0;
      var coords = new List<BigInteger>();
      for (int i = 0; i < ps.Length; i++) for (int n = best[i] + 1; ; n++) { BigInteger q = BigInteger.Pow(ps[i], n * n); if (q > Kmax * m) break; coords.Add(q); }
      int d = coords.Count; bool cond = BigInteger.Pow(m, d) <= N0;
      var seen = new Dictionary<string, long>(); long found = -1;
      for (long x = 0; x <= N0 && cond; x++) {
        BigInteger xx = D * x; var key = string.Join(",", coords.Select(q => (int)((m * (xx % q)) / q)));
        if (seen.TryGetValue(key, out long x0)) { found = x - x0; break; } seen[key] = x;
      }
      Func<BigInteger, bool> inBall = kv => { foreach (var p in ps) for (int n = 1; ; n++) { BigInteger q = BigInteger.Pow(p, n * n); if (q > kv * k) break; BigInteger r = kv % q; BigInteger dd = BigInteger.Min(r, q - r); if (dd * k >= q) return false; } return true; };
      bool ok = found > 0 && inBall(D * found) && found <= N0;
      Console.WriteLine($"S={{{string.Join(",", ps)}}} delta=1/{k} best a=[{string.Join(",", best)}] (forced [{string.Join(",", af)}]) D={D} M={Mb} d={d} m^d<=2^M:{cond} pigeon t={found} t<=2^M and P_S(Dt)<delta: {ok}");
    }
  }
}
