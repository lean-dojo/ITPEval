;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__048, "Dirichlet's Theorem": for every positive
;; natural modulus and every coprime natural residue, the primes congruent to
;; that residue modulo the modulus are unbounded. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-048-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (hundred-theorems-048-no-divisor-from-p n (+ d 1)))
    t))

(defun hundred-theorems-048-primep (n)
  (and (natp n)
       (< 1 n)
       (hundred-theorems-048-no-divisor-from-p n 2)))

(defun hundred-theorems-048-has-common-divisor-through-p (a b d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp a)
           (natp b)
           (natp d)
           (<= 2 d))
      (or (and (equal (mod a d) 0)
               (equal (mod b d) 0))
          (hundred-theorems-048-has-common-divisor-through-p
           a b (- d 1)))
    nil))

(defun hundred-theorems-048-coprimep (a b)
  (and (natp a)
       (natp b)
       (not (and (equal a 0)
                 (equal b 0)))
       (not (hundred-theorems-048-has-common-divisor-through-p
             a b (+ a b)))))

(defun hundred-theorems-048-congruent-p (x y modulus)
  (and (natp x)
       (natp y)
       (natp modulus)
       (if (equal modulus 0)
           (equal x y)
         (equal (mod x modulus)
                (mod y modulus)))))

(defun-sk hundred-theorems-048-prime-above-in-class-exists-p
  (bound modulus residue)
  (exists (p)
    (and (natp p)
         (< bound p)
         (hundred-theorems-048-primep p)
         (hundred-theorems-048-congruent-p p residue modulus))))

(defun-sk hundred-theorems-048-dirichlets-theorem-statement ()
  (forall (modulus residue bound)
    (implies
     (and (natp modulus)
          (natp residue)
          (natp bound)
          (< 0 modulus)
          (hundred-theorems-048-coprimep residue modulus))
     (hundred-theorems-048-prime-above-in-class-exists-p
      bound modulus residue))))

(value-triple :itpeval-statement-checked)
:q
