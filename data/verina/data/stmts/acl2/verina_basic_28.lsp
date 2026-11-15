;; Statement-only formalization of VERINA corpus artifact verina_basic_28,
;; catalog title "isPrime": a deterministic natural-number divisor scan
;; returns whether an input at least two is prime, with its complete
;; range-based correctness contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition and Nat input domain are represented together.

(defun verina-basic-28-is-prime-precond (n)
  (and
   (natp n)
   (<= 2 n)))

;; This is the source-local CHECK recursion. FUEL is initialized to the input
;; bound N. Each recursive call increments I and decrements FUEL, while the
;; tests retain their source order: exhausted fuel, square above N, divisor
;; found, and recursive continuation.

(defun verina-basic-28-check (n i fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      t
    (if (> (* i i) n)
        t
      (if (equal (mod n i) 0)
          nil
        (verina-basic-28-check
         n
         (+ i 1)
         (- fuel 1))))))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. Passing N as fuel and starting at divisor two exactly reproduces
;; the complete executable source implementation.

(defun verina-basic-28-is-prime (n)
  (verina-basic-28-check n 2 n))

(defun verina-basic-28-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This is List.range' START LENGTH: START, ..., START + LENGTH - 1.

(defun verina-basic-28-range-from (start length)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      nil
    (cons
     start
     (verina-basic-28-range-from
      (+ start 1)
      (- length 1)))))

;; These two structural predicates are the source List.all and List.any
;; divisor tests on the generated range.

(defun verina-basic-28-all-nondivisors-p (n divisors)
  (declare (xargs :measure (acl2-count divisors)))
  (if (consp divisors)
      (and
       (not (equal (mod n (car divisors)) 0))
       (verina-basic-28-all-nondivisors-p
        n
        (cdr divisors)))
    (equal divisors nil)))

(defun verina-basic-28-any-divisor-p (n divisors)
  (declare (xargs :measure (acl2-count divisors)))
  (if (consp divisors)
      (or
       (equal (mod n (car divisors)) 0)
       (verina-basic-28-any-divisor-p
        n
        (cdr divisors)))
    nil))

;; NFIX of the integer difference is Lean natural-number subtraction. Thus the
;; generated list is exactly List.range' 2 (n - 2), namely 2 through n - 1
;; for every input satisfying the precondition.

(defun verina-basic-28-candidate-divisors (n)
  (verina-basic-28-range-from
   2
   (nfix (- n 2))))

;; This preserves both source postcondition implications. A true result
;; requires every candidate to be a nondivisor, and a false result requires
;; at least one candidate divisor.

(defun verina-basic-28-is-prime-postcond (n result)
  (let ((divisors
         (verina-basic-28-candidate-divisors n)))
    (and
     (natp n)
     (verina-basic-28-bool-p result)
     (implies
      result
      (verina-basic-28-all-nondivisors-p
       n
       divisors))
     (implies
      (not result)
      (verina-basic-28-any-divisor-p
       n
       divisors)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the full Nat domain, applies the source precondition, and connects the
;; complete postcondition to the exact executable result.

(defun-sk verina-basic-28-is-prime-spec-satisfied-statement ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-28-is-prime-precond n))
     (verina-basic-28-is-prime-postcond
      n
      (verina-basic-28-is-prime n)))))

(value-triple :itpeval-statement-checked)
:q
