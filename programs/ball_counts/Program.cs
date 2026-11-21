using System;
using System.Collections.Generic;
using System.Diagnostics;

class P {
  // Count k in [0,X] with ||k / p^(j^2)|| < 1/R for ALL j >= 1 (strict), exactly, by lifting residues level by level (DFS).
  static Int128 X; static int R; static int p; static int J; static Int128[] q;
  static Int128 total;
  static Int128 CeilDiv(Int128 a, Int128 b) => (a + b - 1) / b;
  static void Dfs(int j, Int128 u) {            // u is an admissible residue mod q[j-1] (j-1 levels done)
    if (j > J) { if (u <= X) total += (X - u) / q[J] + 1; return; }
    Int128 qj = q[j], qp = q[j - 1];
    Int128 a = CeilDiv(qj, R) - 1;               // x admissible iff x <= a or x >= qj - a
    // lower arc: x = u + t*qp in [0,a]
    for (Int128 x = u; x <= a && x < qj; x += qp) Dfs(j + 1, x);
    // upper arc: x in [qj-a, qj-1], x ≡ u (mod qp)
    Int128 lo = qj - a; if (lo <= a) lo = a + 1;  // avoid double counting when arcs overlap (a >= qj/2 cannot happen for R>=3)
    Int128 first = u + CeilDiv(lo - u > 0 ? lo - u : 0, qp) * qp;
    for (Int128 x = first; x < qj; x += qp) Dfs(j + 1, x);
  }
  static Int128 Count(int prime, int r, Int128 Xmax) {
    p = prime; R = r; X = Xmax;
    var qs = new List<Int128> { 1 };
    for (int j = 1; ; j++) { Int128 v = 1; for (int i = 0; i < j * j; i++) v *= p; if (v > (Int128)R * X) break; qs.Add(v); }
    q = qs.ToArray(); J = q.Length - 1; total = 0;
    Dfs(1, 0);
    return total;
  }
  static void Main() {
    var sw = Stopwatch.StartNew();
    // sanity: small brute-force comparison
    foreach (var (pp, rr, xx) in new[] { (2, 20, 100000L), (3, 20, 100000L), (2, 5, 5000L), (3, 7, 50000L), (5, 10, 200000L) }) {
      long brute = 0;
      for (long k = 0; k <= xx; k++) {
        bool ok = true;
        for (int j = 1; ; j++) {
          Int128 qq = 1; for (int i = 0; i < j * j; i++) qq *= pp;
          if (qq > (Int128)rr * xx) break;
          Int128 rem = k % qq; Int128 d = rem < qq - rem ? rem : qq - rem;
          if (d * rr >= qq) { ok = false; break; }
        }
        if (ok) brute++;
      }
      Console.WriteLine($"sanity p={pp} R={rr} X={xx}: brute={brute} dfs={Count(pp, rr, xx)}");
    }
    Console.WriteLine($"X=1e12, r=1/20: |A| (prime 3) = {Count(3, 20, 1000000000000L)}   |B'| (prime 2) = {Count(2, 20, 1000000000000L)}   [{sw.Elapsed.TotalSeconds:F1}s]");
    Console.WriteLine($"X=1e15, r=1/40: |A| (prime 3) = {Count(3, 40, 1000000000000000L)}   |B'| (prime 2) = {Count(2, 40, 1000000000000000L)}   [{sw.Elapsed.TotalSeconds:F1}s]");
  }
}
