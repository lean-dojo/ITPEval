;; Statement-only formalization of miniF2F corpus artifact amc12b_2021_p1:
;; the set of all integers x satisfying |x| < 3*pi has cardinality 19,
;; with pi represented exactly by its Gregory-Leibniz lower Dedekind cut.
;; This file contains no proof.

(in-package "ACL2")

;; The first TERMS summands of
;;
;;   1 - 1/3 + 1/5 - 1/7 + ...
;;
;; are rational numbers. Prefixes with an even positive number of terms end
;; in a negative summand and are strict lower approximations to pi/4.
(defun amc12b-2021-p1-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (denominator (+ (* 2 index) 1))
           (unsigned-term (/ 1 denominator))
           (term (if (equal (mod index 2) 0)
                     unsigned-term
                   (- unsigned-term))))
      (+ (amc12b-2021-p1-leibniz-prefix index)
         term))))

(defun amc12b-2021-p1-pi-lower-approximation (n)
  (* 4
     (amc12b-2021-p1-leibniz-prefix
      (+ (* 2 (nfix n)) 2))))

;; This predicate is the exact rational lower cut of pi: by the
;; Gregory-Leibniz identity, q < pi exactly when q is below one of these
;; increasing lower approximations. Thus pi is represented independently,
;; rather than replaced by bounds chosen from the desired integer solutions.
(defun-sk amc12b-2021-p1-pi-lower-cut-p (q)
  (exists (n)
    (and (rationalp q)
         (natp n)
         (< q
            (amc12b-2021-p1-pi-lower-approximation n)))))

;; Since 3 is positive, |x| < 3*pi is equivalent to |x|/3 < pi.
(defun amc12b-2021-p1-member-p (x)
  (and (integerp x)
       (amc12b-2021-p1-pi-lower-cut-p
        (/ (abs x) 3))))

;; Universal extensional equality with MEMBERS rules out non-integer junk and
;; ranges over every integer; it does not assume a finite search interval.
(defun-sk amc12b-2021-p1-exact-members-p (members)
  (forall (x)
    (iff (member-equal x members)
         (amc12b-2021-p1-member-p x))))

;; A duplicate-free true list extensionally equal to the pi-defined integer
;; predicate has length 19 exactly when that set has cardinality 19.
(defun-sk amc12b-2021-p1-statement ()
  (exists (members)
    (and (true-listp members)
         (no-duplicatesp-equal members)
         (amc12b-2021-p1-exact-members-p members)
         (equal (len members) 19))))

(value-triple :itpeval-statement-checked)
:q
