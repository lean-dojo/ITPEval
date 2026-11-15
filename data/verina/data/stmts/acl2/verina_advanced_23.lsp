;; Statement-only formalization of VERINA corpus artifact verina_advanced_23,
;; "isPowerOfTwo": a deterministic integer computation decides whether its
;; input is a positive power of two, together with its Boolean correctness
;; contract. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True; the Int input domain is explicit in the
;; final correctness statement.

(defun verina-advanced-23-is-power-of-two-precond (n)
  (declare (ignore n))
  t)

;; This is the source's fuel-bounded local recursion. On every reachable call,
;; m is positive and fuel starts at abs(n); dividing an even m by two reaches
;; 1 before that fuel can expire, so the fuel preserves the exact computation.

(defun verina-advanced-23-is-power-of-two-aux (m fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (integerp m))
          (not (natp fuel)))
      nil
    (if (equal fuel 0)
        nil
      (if (equal m 1)
          t
        (if (not (equal (mod m 2) 0))
            nil
          (verina-advanced-23-is-power-of-two-aux
           (floor m 2)
           (- fuel 1)))))))

(defun verina-advanced-23-is-power-of-two (n)
  (if (not (integerp n))
      nil
    (if (<= n 0)
        nil
      (verina-advanced-23-is-power-of-two-aux
       n
       (abs n)))))

;; Exact recursive translation of the source Int-base, Nat-exponent power
;; helper used by the postcondition.

(defun verina-advanced-23-pow (base exp)
  (declare (xargs :measure (nfix exp)))
  (if (or (not (integerp base))
          (not (natp exp)))
      1
    (if (equal exp 0)
        1
      (* base
         (verina-advanced-23-pow base (- exp 1))))))

(defun-sk verina-advanced-23-positive-power-of-two-p (n)
  (exists (x)
    (and
     (natp x)
     (equal (verina-advanced-23-pow 2 x) n)
     (> n 0))))

(defun verina-advanced-23-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-23-is-power-of-two-postcond (n result)
  (and
   (integerp n)
   (verina-advanced-23-bool-p result)
   (if result
       (verina-advanced-23-positive-power-of-two-p n)
     (not
      (verina-advanced-23-positive-power-of-two-p n)))))

(defun
    verina-advanced-23-is-power-of-two-spec-satisfied-statement
    (n)
  (implies
   (and
    (integerp n)
    (verina-advanced-23-is-power-of-two-precond n))
   (verina-advanced-23-is-power-of-two-postcond
    n
    (verina-advanced-23-is-power-of-two n))))

(value-triple :itpeval-statement-checked)
:q
