using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;

// Exact replay of E = #{(a,b,a',b') in A x B x A x B : a-b = a'-b'} = sum_h rA(h) rB(h)
// A = {k in [0,X]: P_3(k) < 1/R}, B = {k in [0,X]: P_2(k) < 1/R}, r_S(h) = #{(x,x') in S^2 : x - x' = h}.
class Ball {
  public int p, R; public long X; public long[] q; public int J; public long[] a, a2;
  public Ball(int p, int R, long X) {
    this.p = p; this.R = R; this.X = X;
    var qs = new List<long> { 1 };
    for (int j = 1; ; j++) { BigInteger v = BigInteger.Pow(p, j * j); if (v > (BigInteger)R * X) break; qs.Add((long)v); }
    q = qs.ToArray(); J = q.Length - 1;
    a = new long[J + 1]; a2 = new long[J + 1];
    for (int j = 1; j <= J; j++) { a[j] = (q[j] + R - 1) / R - 1; a2[j] = (2 * q[j] + R - 1) / R - 1; }   // dist < q/R  <=> dist <= a ; dist < 2q/R <=> dist <= a2
  }
  // ---- pair count: #{x in [0, X-h] : x in ball, x+h in ball}, h >= 0 ----
  long hh; long tot; long[] lo = new long[8], hi = new long[8];
  public long PairCount(long h) { hh = h; tot = 0; Dfs(1, 0); return tot; }
  static void Shift(long l, long r, long hm, long qj, List<(long, long)> res) {   // {x in [0,qj): l <= x+hm mod qj ... } : x in [l-hm, r-hm] mod qj
    long L = l - hm, Rr = r - hm;
    if (L >= 0) res.Add((L, Rr));
    else if (Rr < 0) res.Add((L + qj, Rr + qj));
    else { res.Add((0, Rr)); res.Add((L + qj, qj - 1)); }
  }
  void Dfs(int j, long u) {
    if (j > J) { long lim = X - hh; if (u <= lim) tot += (lim - u) / q[J] + 1; return; }
    long qj = q[j], qp = q[j - 1], aj = a[j], hm = hh % qj;
    var arcX = new (long, long)[] { (0, aj), (qj - aj, qj - 1) };
    var arcY = new List<(long, long)>(4);
    foreach (var (l, r) in arcX) Shift(l, r, hm, qj, arcY);
    foreach (var (l1, r1) in arcX) foreach (var (l2, r2) in arcY) {
      long l = Math.Max(l1, l2), r = Math.Min(r1, r2);
      if (l > r) continue;
      long first = l + (((u - l) % qp) + qp) % qp;
      if (j == J) {   // last level: count leaves arithmetically; contribution of x is K+1 if x<=c else K (lim = K*q_J + c)
        if (first > r) continue;
        long lim = X - hh; if (lim < 0) continue;
        long K = lim / qj, c = lim % qj;
        long n = (r - first) / qp + 1;
        long top = Math.Min(r, c);
        long m = first <= top ? (top - first) / qp + 1 : 0;
        tot += n * K + m;
      } else {
        for (long x = first; x <= r; x += qp) Dfs(j + 1, x);
      }
    }
  }
  // ---- element count and listing (for brute force) ----
  public void List(List<long> outl) { Lst(1, 0, outl); }
  void Lst(int j, long u, List<long> outl) {
    if (j > J) { for (long x = u; x <= X; x += q[J]) outl.Add(x); return; }
    long qj = q[j], qp = q[j - 1], aj = a[j];
    for (long x = u; x <= aj && x < qj; x += qp) Lst(j + 1, x, outl);
    long lo2 = Math.Max(qj - aj, aj + 1); long first = u + (lo2 - u > 0 ? (lo2 - u + qp - 1) / qp : 0) * qp;
    for (long x = first; x < qj; x += qp) Lst(j + 1, x, outl);
  }
  // ---- difference-ball membership (dist(h, q_j Z)*R < 2 q_j for all j) ----
  public bool InDiffBall(long h) {
    for (int j = 1; j <= J; j++) { long m = h % q[j]; long d = Math.Min(m, q[j] - m); if (d > a2[j]) return false; }
    return true;
  }
  // enumerate h in [1,X] in the difference ball (2-adic or 3-adic) and call f
  public void EnumDiff(Action<long> f) { Ed(1, 0, f); }
  void Ed(int j, long u, Action<long> f) {
    if (j > J) { for (long x = (u == 0 ? q[J] : u); x <= X; x += q[J]) f(x); return; }
    long qj = q[j], qp = q[j - 1], aj = a2[j];
    for (long x = u; x <= aj && x < qj; x += qp) Ed(j + 1, x, f);
    long lo2 = Math.Max(qj - aj, aj + 1); long first = u + (lo2 - u > 0 ? (lo2 - u + qp - 1) / qp : 0) * qp;
    for (long x = first; x < qj; x += qp) Ed(j + 1, x, f);
  }
}

class P {
  static BigInteger ComputeE(int R, long X, bool verbose, out long nA, out long nB, out long candidates, out long survivors) {
    var A = new Ball(3, R, X); var B = new Ball(2, R, X);
    nA = A.PairCount(0); nB = B.PairCount(0);
    BigInteger sum = 0; long cand = 0, surv = 0;
    long cnt = 0; var sw = Stopwatch.StartNew();
    B.EnumDiff(h => {
      cand++;
      if (!A.InDiffBall(h)) return;
      long rb = B.PairCount(h); if (rb == 0) return;
      long ra = A.PairCount(h); if (ra == 0) return;
      surv++; sum += (BigInteger)ra * rb;
      if (verbose && (++cnt % 1000000 == 0)) Console.Error.WriteLine($"   ... {surv} survivors, h={h}, {sw.Elapsed.TotalSeconds:F0}s");
    });
    candidates = cand; survivors = surv;
    return (BigInteger)nA * nB + 2 * sum;
  }
  static void Main(string[] args) {
    string mode = args[0];
    if (mode == "test") {
      foreach (var (R, X) in new[] { (20, 200000L), (20, 1000000L), (10, 300000L), (7, 100000L), (20, 3000000L) }) {
        var A = new Ball(3, R, X); var B = new Ball(2, R, X);
        var la = new List<long>(); var lb = new List<long>(); A.List(la); B.List(lb);
        // brute-force E via difference histogram
        var d = new Dictionary<long, long>();
        foreach (var x in la) foreach (var y in lb) { long k = x - y; d.TryGetValue(k, out long c); d[k] = c + 1; }
        BigInteger brute = 0; foreach (var c in d.Values) brute += (BigInteger)c * c;
        var sw = Stopwatch.StartNew();
        var E = ComputeE(R, X, false, out long nA, out long nB, out long cand, out long surv);
        Console.WriteLine($"R={R} X={X}: |A|={la.Count}/{nA} |B|={lb.Count}/{nB} E brute={brute} E new={E} equal={brute == E} (cand {cand}, surv {surv}, {sw.Elapsed.TotalSeconds:F1}s)");
      }
    } else {
      int R = int.Parse(args[1]); long X = long.Parse(args[2]);
      var sw = Stopwatch.StartNew();
      var E = ComputeE(R, X, true, out long nA, out long nB, out long cand, out long surv);
      BigInteger num = (BigInteger)nA * nB; num *= num;
      BigInteger L = (num + E - 1) / E;
      BigInteger t = 2 * L - 2 * (BigInteger)X - 2;
      Console.WriteLine($"R={R} X={X}: |A|={nA} |B'|={nB} E={E} L=ceil((|A||B'|)^2/E)={L}  max|t|=2L-2X-2={t}  candidates={cand} survivors={surv} time={sw.Elapsed.TotalSeconds:F1}s");
    }
  }
}
