using System; using System.Linq; using System.Numerics;
class P {
  static int Ceil2(BigInteger v) { int h = 0; while ((BigInteger.One << h) < v) h++; return h; }
  static void Main() {
    var sets = new int[][]{ new[]{2}, new[]{3}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{2,3,5,7}, new[]{2,5,7}, new[]{101}, new[]{2,101}, new[]{2,3,5,7,11,13} };
    foreach (var S in sets) {
      double A = S.Sum(p => 1 / Math.Sqrt(Math.Log(p, 2))); double a2 = Math.Max(1, A * A);
      int worse = 0, tested = 0; double worstRatio = 0; int firstWorse = -1;
      for (int k = 2; k <= 5000; k++) {
        int h = Ceil2(2 * k);
        var a = S.Select(p => { int aa = 0; while (BigInteger.Pow(p, 2 * aa + 1) <= k) aa++; return aa; }).ToArray();
        double alpha = a.Sum(), Delta = S.Select((p, i) => (double)a[i] * a[i] * Math.Log(p, 2)).Sum();
        double Q = (double)h * h * A * A - 4 * (h * alpha - Delta - h);
        double ts = (h * A + Math.Sqrt(Q)) / 2;
        double B = Math.Max(Delta, ts * ts - h + 1);                       // log2 of Scope B bound
        double U = Math.Ceiling(a2 * h * h + a2 * h);                       // log2 of Theorem upper' bound (2^L)
        tested++; if (Q < 0) Console.WriteLine("NEGATIVE DISCRIMINANT");
        if (B > U) { worse++; if (firstWorse < 0) firstWorse = k; }
        worstRatio = Math.Max(worstRatio, B / U);
      }
      Console.WriteLine($"S={{{string.Join(",", S)}}}: delta=1/k, k=2..5000 ({tested}): ScopeB worse than Upper' in {worse} cases (first k={firstWorse}); max ratio B/Upper' = {worstRatio:F3}");
    }
  }
}
