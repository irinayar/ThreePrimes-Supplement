using System; using System.Linq;
// Expected number of records of P_S in the Poisson model with the intensity of the independence model H.
// Lambda(x,delta) = (x/D) (2/m)^{C(x)}, C(x) = sum_p max(0, sqrt(log_p(x m)) - a_p - off), made nondecreasing in x.
// P(jump between delta_i and delta_{i+1}) = 1 - int exp(-Lambda_i) dLambda_{i+1};  E[#records, ell in bin] = sum of the jump probabilities.
class P {
  static void Main(string[] a) {
    int[] S = a[0].Split(',').Select(int.Parse).ToArray(); double off = a.Length > 1 ? double.Parse(a[1]) : 0.5;
    double l0 = 1.0, l1 = a.Length > 2 ? double.Parse(a[2]) : 18.5, dl = 0.01, dy = 0.02, ymax = a.Length > 3 ? double.Parse(a[3]) : 480;
    int ny = (int)(ymax / dy) + 1; double ln2 = Math.Log(2); double[] lp = S.Select(p => Math.Log(p)).ToArray();
    int nl = (int)((l1 - l0) / dl) + 1; double[][] LAM = new double[nl][]; // Lambda values (not log), capped at 1e30
    for (int i = 0; i < nl; i++) {
      double ell = l0 + i * dl; double delta = Math.Pow(2, -ell); double m = Math.Ceiling(1.0 / delta - 1e-12);
      int[] ap = new int[S.Length]; double lnD = 0; for (int s = 0; s < S.Length; s++) { int e = 0; while (!(Math.Pow(S[s], -(2.0 * e + 1)) < delta)) e++; ap[s] = e; lnD += e * e * lp[s]; }
      double lm = Math.Log(m), l2m = Math.Log(2.0 / m); double[] L = new double[ny]; double run = 0;
      for (int j = 0; j < ny; j++) { double y = j * dy; double lx = y * ln2; double C = 0; for (int s = 0; s < S.Length; s++) { double nn = Math.Sqrt((lx + lm) / lp[s]) - ap[s] - off; if (nn > 0) C += nn; }
        double lnL = lx - lnD + C * l2m; double v = lnL > 69 ? 1e30 : Math.Exp(lnL); if (v > run) run = v; L[j] = run; }
      LAM[i] = L;
    }
    // sanity: int exp(-L_i) dL_i
    double[] jump = new double[nl - 1];
    for (int i = 0; i + 1 < nl; i++) {
      var A = LAM[i]; var B = LAM[i + 1]; double same = A[0] > 0 ? B[0] * (1 - Math.Exp(-A[0])) / A[0] : 0, self = 1 - Math.Exp(-A[0]);
      for (int j = 0; j + 1 < ny; j++) { double e = Math.Exp(-0.5 * (A[j] + A[j + 1])); if (A[j] > 1e29) break; same += e * (B[j + 1] - B[j]); self += e * (A[j + 1] - A[j]); }
      if (i == 0) Console.WriteLine($"# sanity int exp(-L) dL = {self:F4} (should be about 1)");
      jump[i] = Math.Max(0, 1 - same);
    }
    Console.WriteLine("# S={" + string.Join(",", S) + "} off=" + off);
    for (int L = (int)l0; L < (int)l1; L++) { double s = 0; for (int i = 0; i < nl - 1; i++) { double ell = l0 + i * dl; if (ell >= L && ell < L + 1) s += jump[i]; } Console.WriteLine($"{L} {s:F2}"); }
    double tot = 0; for (int i = 0; i < nl - 1; i++) tot += jump[i]; Console.WriteLine($"total {tot:F1}");
  }
}
