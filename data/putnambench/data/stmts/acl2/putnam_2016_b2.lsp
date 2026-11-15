;; Statement-only formalization of PutnamBench artifact putnam_2016_b2:
;; if S(N) counts the positive squarish integers at most N, then
;; S(N) / N^(3/4) tends to 4/3. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For positive S(N), the published asymptotic is equivalent to
;;
;;              S(N)^4 / N^3  ->  (4/3)^4 = 256/81.
;;
;; This normalization uses only exact rational arithmetic. It preserves the
;; stated constants alpha=3/4 and beta=4/3 without introducing a surrogate
;; real-power operation or an artificial model of the real continuum.

(defun p2016b2-square-up-to-p (n root)
  (declare (xargs :measure (nfix root)))
  (if (zp root)
      (equal n 0)
    (or
     (equal n (* root root))
     (p2016b2-square-up-to-p n (- root 1)))))

(defun p2016b2-square-p (n)
  (and
   (natp n)
   (p2016b2-square-up-to-p n n)))

(defun p2016b2-nearest-square-distance (n root)
  (declare (xargs :measure (nfix root)))
  (if (zp root)
      (abs n)
    (let ((current (abs (- n (* root root))))
          (previous
           (p2016b2-nearest-square-distance
            n (- root 1))))
      (if (< current previous)
          current
        previous))))

(defun p2016b2-squarish-p (n)
  (and
   (posp n)
   (or
    (p2016b2-square-p n)
    (p2016b2-square-p
     (p2016b2-nearest-square-distance n n)))))

(defun p2016b2-count (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (if (p2016b2-squarish-p n) 1 0)
       (p2016b2-count (- n 1)))))

(defun p2016b2-normalized-fourth-power (n)
  (/ (expt (p2016b2-count n) 4)
     (expt n 3)))

(defun-sk p2016b2-limit-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (posp n)
      (<= cutoff n))
     (<
      (abs
       (-
        (p2016b2-normalized-fourth-power n)
        (/ 256 81)))
      epsilon))))

(defun-sk p2016b2-limit-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p2016b2-limit-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-2016-b2-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p2016b2-limit-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
