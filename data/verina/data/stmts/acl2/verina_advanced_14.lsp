;; Statement-only formalization of VERINA corpus artifact verina_advanced_14,
;; "ifPowerOfFour": a deterministic natural-number recursion decides whether
;; its input is an exact power of four, together with its Boolean correctness
;; contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True; the Nat input domain is explicit in the
;; final statement predicate.

(defun verina-advanced-14-if-power-of-four-precond (n)
  (declare (ignore n))
  t)

;; Each recursive source call replaces n by floor(n / 4), so for natural n at
;; least two the residual strictly decreases. Initial fuel n therefore cannot
;; expire before the source recursion terminates and does not add a cutoff.

(defun verina-advanced-14-if-power-of-four-helper-aux
    (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (not (natp n))
      nil
    (if (equal n 0)
        nil
      (if (equal n 1)
          t
        (if (equal (mod n 4) 0)
            (if (zp fuel)
                nil
              (verina-advanced-14-if-power-of-four-helper-aux
               (floor n 4)
               (- fuel 1)))
          nil)))))

(defun verina-advanced-14-if-power-of-four-helper (n)
  (verina-advanced-14-if-power-of-four-helper-aux
   n
   (nfix n)))

(defun verina-advanced-14-if-power-of-four (n)
  (verina-advanced-14-if-power-of-four-helper n))

(defun-sk verina-advanced-14-power-of-four-p (n)
  (exists (m)
    (and
     (natp m)
     (equal n (expt 4 m)))))

(defun verina-advanced-14-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-14-if-power-of-four-postcond
    (n result)
  (and
   (natp n)
   (verina-advanced-14-bool-p result)
   (iff
    result
    (verina-advanced-14-power-of-four-p n))))

(defun
    verina-advanced-14-if-power-of-four-spec-satisfied-statement
    (n)
  (implies
   (and
    (natp n)
    (verina-advanced-14-if-power-of-four-precond n))
   (verina-advanced-14-if-power-of-four-postcond
    n
    (verina-advanced-14-if-power-of-four n))))

(value-triple :itpeval-statement-checked)
:q
