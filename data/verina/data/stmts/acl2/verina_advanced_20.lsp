;; Statement-only formalization of VERINA corpus artifact verina_advanced_20,
;; "isItEight": a deterministic integer computation returns true exactly when
;; the input is divisible by 8 or the decimal expansion of its absolute value
;; contains the digit 8, together with its Boolean correctness contract. This
;; file contains no proof.

(in-package "ACL2")

;; The source precondition is True; the Int input domain is explicit in the
;; final correctness statement.

(defun verina-advanced-20-is-it-eight-precond (n)
  (declare (ignore n))
  t)

;; For natural m, each recursive source call replaces a positive residual by
;; floor(m / 10). Initial fuel m therefore cannot expire before the source
;; recursion terminates and does not add a cutoff to its behavior.

(defun verina-advanced-20-has-digit-eight-aux (m fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (not (natp m))
      nil
    (if (zp m)
        nil
      (if (equal (mod m 10) 8)
          t
        (if (zp fuel)
            nil
          (verina-advanced-20-has-digit-eight-aux
           (floor m 10)
           (- fuel 1)))))))

(defun verina-advanced-20-has-digit-eight (m)
  (verina-advanced-20-has-digit-eight-aux
   m
   (nfix m)))

(defun verina-advanced-20-is-it-eight (n)
  (or
   (equal (mod n 8) 0)
   (verina-advanced-20-has-digit-eight (abs n))))

;; This predicate separately preserves the source postcondition's existential
;; quantification over all natural decimal positions.

(defun-sk verina-advanced-20-has-eight-at-some-position-p (n)
  (exists (i)
    (and
     (natp i)
     (equal
      (mod (floor (abs n) (expt 10 i)) 10)
      8))))

(defun verina-advanced-20-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-20-is-it-eight-postcond (n result)
  (and
   (integerp n)
   (verina-advanced-20-bool-p result)
   (iff
    (or
     (equal (mod n 8) 0)
     (verina-advanced-20-has-eight-at-some-position-p n))
    result)))

(defun verina-advanced-20-is-it-eight-spec-satisfied-statement (n)
  (implies
   (and
    (integerp n)
    (verina-advanced-20-is-it-eight-precond n))
   (verina-advanced-20-is-it-eight-postcond
    n
    (verina-advanced-20-is-it-eight n))))

(value-triple :itpeval-statement-checked)
:q
