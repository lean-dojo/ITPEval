;; Statement-only formalization of VERINA corpus artifact verina_advanced_10,
;; "findExponents": a deterministic prime-list scan computes each prime's
;; exponent while successively dividing it out of a positive natural number.
;; This file contains no proof.

(in-package "ACL2")

;; This bounded divisor scan is equivalent to Nat.Prime on natural numbers.

(defun verina-advanced-10-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (verina-advanced-10-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun verina-advanced-10-prime-p (number)
  (and (natp number)
       (< 1 number)
       (verina-advanced-10-no-divisor-from-p number 2)))

(defun verina-advanced-10-prime-list-p (primes)
  (if (consp primes)
      (and
       (verina-advanced-10-prime-p (car primes))
       (verina-advanced-10-prime-list-p (cdr primes)))
    (equal primes nil)))

;; The fuel is initialized to n. Whenever division recurs, the positive
;; residual strictly decreases, so n steps exactly implement the source
;; well-founded recursion rather than adding a cutoff to its behavior.

(defun verina-advanced-10-remove-prime-factor-aux (n p fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (and (natp n)
           (natp p)
           (< 1 p)
           (< 0 n)
           (not (zp fuel)))
      (if (equal (mod n p) 0)
          (verina-advanced-10-remove-prime-factor-aux
           (floor n p) p (- fuel 1))
        n)
    n))

(defun verina-advanced-10-remove-prime-factor (n p)
  (verina-advanced-10-remove-prime-factor-aux n p (nfix n)))

(defun verina-advanced-10-remove-all-prime-factors (n primes)
  (if (consp primes)
      (verina-advanced-10-remove-all-prime-factors
       (verina-advanced-10-remove-prime-factor n (car primes))
       (cdr primes))
    n))

(defun verina-advanced-10-find-exponents-precond (n primes)
  (and
   (natp n)
   (< 0 n)
   (consp primes)
   (verina-advanced-10-prime-list-p primes)
   (no-duplicatesp-equal primes)
   (equal
    (verina-advanced-10-remove-all-prime-factors n primes)
    1)))

;; A count-factor result is the ACL2 pair (count . residual). As above,
;; source recursion strictly lowers residual n whenever it continues, so
;; starting with fuel n preserves the exact computation on natural inputs.

(defun verina-advanced-10-count-factor-aux (n p count fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (equal n 0)
      (cons count 0)
    (if (and (natp n)
             (natp p)
             (natp count)
             (< 1 p)
             (< 0 n)
             (not (zp fuel)))
        (if (equal (mod n p) 0)
            (verina-advanced-10-count-factor-aux
             (floor n p) p (+ count 1) (- fuel 1))
          (cons count n))
      (cons count n))))

(defun verina-advanced-10-count-factor (n p count)
  (verina-advanced-10-count-factor-aux n p count (nfix n)))

(defun verina-advanced-10-count-factors (n primes)
  (if (consp primes)
      (let ((count-and-residual
             (verina-advanced-10-count-factor
              n (car primes) 0)))
        (cons
         (cons (car primes) (car count-and-residual))
         (verina-advanced-10-count-factors
          (cdr count-and-residual) (cdr primes))))
    nil))

(defun verina-advanced-10-find-exponents (n primes)
  (verina-advanced-10-count-factors n primes))

(defun verina-advanced-10-nat-pair-list-p (pairs)
  (if (consp pairs)
      (and
       (consp (car pairs))
       (natp (car (car pairs)))
       (natp (cdr (car pairs)))
       (verina-advanced-10-nat-pair-list-p (cdr pairs)))
    (equal pairs nil)))

(defun verina-advanced-10-product-of-powers-fold (pairs accumulator)
  (if (consp pairs)
      (verina-advanced-10-product-of-powers-fold
       (cdr pairs)
       (* accumulator
          (expt (car (car pairs))
                (cdr (car pairs)))))
    accumulator))

(defun verina-advanced-10-result-primes-from-input-p
    (pairs primes)
  (if (consp pairs)
      (and
       (member-equal (car (car pairs)) primes)
       (verina-advanced-10-result-primes-from-input-p
        (cdr pairs) primes))
    (equal pairs nil)))

(defun verina-advanced-10-result-contains-prime-p (p pairs)
  (if (consp pairs)
      (or
       (equal (car (car pairs)) p)
       (verina-advanced-10-result-contains-prime-p
        p (cdr pairs)))
    nil))

(defun verina-advanced-10-every-input-prime-appears-p
    (primes pairs)
  (if (consp primes)
      (and
       (verina-advanced-10-result-contains-prime-p
        (car primes) pairs)
       (verina-advanced-10-every-input-prime-appears-p
        (cdr primes) pairs))
    (equal primes nil)))

(defun verina-advanced-10-find-exponents-postcond
    (n primes result)
  (and
   (verina-advanced-10-nat-pair-list-p result)
   (equal
    n
    (verina-advanced-10-product-of-powers-fold result 1))
   (verina-advanced-10-result-primes-from-input-p result primes)
   (verina-advanced-10-every-input-prime-appears-p
    primes result)))

(defun verina-advanced-10-find-exponents-spec-satisfied-statement
    (n primes)
  (implies
   (verina-advanced-10-find-exponents-precond n primes)
   (verina-advanced-10-find-exponents-postcond
    n
    primes
    (verina-advanced-10-find-exponents n primes))))

(value-triple :itpeval-statement-checked)
:q
