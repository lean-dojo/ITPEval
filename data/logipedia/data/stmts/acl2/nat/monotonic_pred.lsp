;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_pred, catalog title "nat.monotonic_pred": the natural-number
;; predecessor function is monotone with respect to natural-number order. This
;; file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-monotonic-pred-predecessor (n)
  (if (zp n)
      0
    (- n 1)))

(defun-sk logipedia-nat-monotonic-pred-statement ()
  (forall (x y)
    (implies
     (and
      (natp x)
      (natp y)
      (<= x y))
     (<= (logipedia-nat-monotonic-pred-predecessor x)
         (logipedia-nat-monotonic-pred-predecessor y)))))

(value-triple :itpeval-statement-checked)
:q
