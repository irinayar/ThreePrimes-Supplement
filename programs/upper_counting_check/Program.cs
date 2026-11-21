using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;

class P {
  // exact: number of n>=1 with p^(n^2) <= 2^B
  static int CountExact(int p, int B) {
    double est = Math.Sqrt(B / Math.Log(p, 2));
    int n = (int)Math.Floor(est);
    BigInteger lim = BigInteger.One << B;
    while (n >= 1 && BigInteger.Pow(p, n*n) > lim) n--;
    while (BigInteger.Pow(p, (n+1)*(n+1)) <= lim) n++;
    return Math.Max(n, 0);
  }
  static void Main() {
    var sets = new int[][]{ new[]{2}, new[]{3}, new[]{5}, new[]{2,3}, new[]{3,5}, new[]{2,3,5}, new[]{2,3,5,7}, new[]{3,5,7}, new[]{101}, new[]{2,3,5,7,11,13} };
    Console.WriteLine("== Part A: exact integer check  h*d_exact(L+h) <= L at L = ceil(a h^2 + a h), a = max(1,c'^2), m = 2^h (worst case), h = 2..120");
    foreach (var S in sets) {
      double c = S.Sum(p => 1/Math.Sqrt(Math.Log(p,2)));
      double a = Math.Max(1.0, c*c);
      bool ok = true; int firstBad = -1; double maxRatio = 0; int cnt = 0;
      for (int h = 2; h <= 120; h++) {
        long L = (long)Math.Ceiling(a*h*h + a*h);
        int B = (int)(L + h);
        long d = 0; foreach (var p in S) d += CountExact(p, B);
        cnt++;
        double ratio = (double)h * d / L; if (ratio > maxRatio) maxRatio = ratio;
        if (h * d > L) { ok = false; if (firstBad < 0) firstBad = h; }
      }
      // also the same test with a deliberately too small exponent a' = 0.9 a to confirm the test can fail
      Console.WriteLine($"S={{{string.Join(",", S)}}} c'={c:F4} a={a:F4} 4s^2/a={4.0*S.Length*S.Length/a:F2}  all ok={ok} firstBad={firstBad} max h*d/L={maxRatio:F4} (h tested {cnt})");
    }
    Console.WriteLine("== Part A': sensitivity: same test with a replaced by 0.8 a (should fail somewhere if the constant is near-sharp for this proof)");
    foreach (var S in sets) {
      double c = S.Sum(p => 1/Math.Sqrt(Math.Log(p,2)));
      double a = 0.8*Math.Max(1.0, c*c);
      int firstBad=-1;
      for (int h = 2; h <= 120; h++) {
        long L = (long)Math.Ceiling(a*h*h + a*h); int B=(int)(L+h);
        long d=0; foreach (var p in S) d += CountExact(p,B);
        if (h*d > L) { firstBad=h; break; }
      }
      Console.WriteLine($"S={{{string.Join(",", S)}}} first failing h with 0.8a: {firstBad}");
    }
    Console.WriteLine("== Part B: end-to-end pigeonhole, exact integer arithmetic");
    var cases = new List<(int[] S,int m)>();
    for (int m = 4; m <= 16; m++) cases.Add((new[]{2}, m));
    for (int m = 4; m <= 4; m++) cases.Add((new[]{2,3}, m));
    foreach (var (S, m) in cases) {
      int h = (int)Math.Ceiling(Math.Log(m,2)); while ((1L<<h) < m) h++; while (h>0 && (1L<<(h-1)) >= m) h--;
      double c = S.Sum(p => 1/Math.Sqrt(Math.Log(p,2))); double a = Math.Max(1.0,c*c);
      int L = (int)Math.Ceiling(a*h*h + a*h); if (L > 22) { Console.WriteLine($"skip S={{{string.Join(",",S)}}} m={m} h={h} L={L}"); continue; }
      long N = 1L<<L;
      // retained coordinates
      var qs = new List<long>();
      foreach (var p in S) for (int n=1;; n++) { BigInteger q = BigInteger.Pow(p,n*n); if (q > (BigInteger)N*m) break; qs.Add((long)q); }
      int d = qs.Count;
      BigInteger boxes = BigInteger.Pow(m,d);
      bool cond = boxes <= N;
      long[] seen = null; var dict = new Dictionary<ulong,long>(); long kFound=-1;
      for (long x=0;x<=N && cond;x++) {
        ulong key=0; foreach (var q in qs) key = key*(ulong)m + (ulong)((m*(x%q))/q);
        if (dict.TryGetValue(key, out long x0)) { kFound = x-x0; break; } dict[key]=x;
      }
      Func<long,bool> inBall = k => { foreach (var p in S) for (int n=1;; n++) { BigInteger q = BigInteger.Pow(p,n*n); if (q > (BigInteger)k*m) break; BigInteger r = k % q; BigInteger dist = BigInteger.Min(r, q-r); if (dist*m >= q) return false; } return true; };
      // ball membership is with respect to strict < 1/m (stronger than < delta/2=1/m? here delta=2/m -> delta/2 = 1/m)
      bool ball = kFound>0 && inBall(kFound);
      long least=-1; for (long k=1;k<=N;k++) if (inBall(k)) { least=k; break; }
      Console.WriteLine($"S={{{string.Join(",",S)}}} m={m} h={h} L={L} N={N} d={d} m^d<=N:{cond} pigeon k={kFound} k<=N:{kFound>=1&&kFound<=N} P_S(k)<1/m (exact):{ball} least k with P_S<1/m = {least}");
    }
  }
}
