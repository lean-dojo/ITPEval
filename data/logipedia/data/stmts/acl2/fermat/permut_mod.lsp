;; Statement-only formalization of Logipedia corpus artifact
;; fermat.permut_mod, catalog title "fermat.permut_mod": for every natural
;; prime p and natural a not divisible by p, multiplication by a modulo p
;; maps the natural indices from 0 through p - 1 into that range injectively.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-fermat-permut-mod-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

(defun-sk logipedia-fermat-permut-mod-prime-divisors-p (p)
  (forall (m)
    (implies
     (and
      (natp m)
      (logipedia-fermat-permut-mod-divides-p m p)
      (< 1 m))
     (equal m p))))

(defun logipedia-fermat-permut-mod-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (logipedia-fermat-permut-mod-prime-divisors-p p)))

(defun-sk logipedia-fermat-permut-mod-range-p (p a)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= i (- p 1)))
     (<= (mod (* a i) p) (- p 1)))))

(defun-sk logipedia-fermat-permut-mod-injective-p (p a)
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i (- p 1))
      (<= j (- p 1))
      (equal (mod (* a i) p)
             (mod (* a j) p)))
     (equal i j))))

(defun logipedia-fermat-permut-mod-statement (p a)
  (implies
   (and
    (natp p)
    (natp a)
    (logipedia-fermat-permut-mod-prime-p p)
    (not (logipedia-fermat-permut-mod-divides-p p a)))
   (and
    (logipedia-fermat-permut-mod-range-p p a)
    (logipedia-fermat-permut-mod-injective-p p a))))

(value-triple :itpeval-statement-checked)
:q
