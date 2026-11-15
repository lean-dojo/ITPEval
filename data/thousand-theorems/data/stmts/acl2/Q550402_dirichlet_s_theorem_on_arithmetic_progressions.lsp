;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q550402, "Dirichlet's theorem on arithmetic
;; progressions": for a positive modulus and an invertible residue class,
;; infinitely many primes lie in that residue class. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A ZMod q element is represented by its unique natural representative below
;; q. Such an element is invertible exactly when its representative is
;; coprime to q.

(defun q550402-has-common-nontrivial-divisor-p
    (left right divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (or (not (natp divisor))
          (< divisor 2))
      nil
    (or
     (and (equal (mod left divisor) 0)
          (equal (mod right divisor) 0))
     (q550402-has-common-nontrivial-divisor-p
      left right (- divisor 1)))))

(defun q550402-coprime-p (left right)
  (and
   (natp left)
   (natp right)
   (not
    (q550402-has-common-nontrivial-divisor-p
     left right (max left right)))))

(defun q550402-has-nontrivial-divisor-p
    (number divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (or (not (natp divisor))
          (< divisor 2))
      nil
    (or
     (equal (mod number divisor) 0)
     (q550402-has-nontrivial-divisor-p
      number (- divisor 1)))))

(defun q550402-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (not
    (q550402-has-nontrivial-divisor-p
     number (- number 1)))))

(defun-sk q550402-prime-above-in-residue-exists-p
    (modulus residue bound)
  (exists (prime)
    (and
     (natp prime)
     (< bound prime)
     (q550402-prime-p prime)
     (equal (mod prime modulus) residue))))

;; For subsets of the naturals, infinitude is equivalent to unboundedness.
;; Thus the universal bound and existential prime remain internal quantifiers.

(defun-sk q550402-primes-in-residue-unbounded-p
    (modulus residue)
  (forall (bound)
    (implies
     (natp bound)
     (q550402-prime-above-in-residue-exists-p
      modulus residue bound))))

(defun thousand-theorems-q550402-dirichlet-statement
    (modulus residue)
  (implies
   (and
    (natp modulus)
    (< 0 modulus)
    (natp residue)
    (< residue modulus)
    (q550402-coprime-p residue modulus))
   (q550402-primes-in-residue-unbounded-p
    modulus residue)))

(value-triple :itpeval-statement-checked)
:q
