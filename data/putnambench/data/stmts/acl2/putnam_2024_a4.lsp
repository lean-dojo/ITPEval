;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4:
;; the primes p > 5 admitting a rearrangement of 1,a,...,a^(p-5) whose
;; consecutive differences are all congruent to one nonzero residue modulo p
;; are exactly p = 7. This file contains no proof.

(in-package "ACL2")

(defun putnam-2024-a4-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (putnam-2024-a4-no-divisor-from-p n (+ d 1)))
    t))

(defun putnam-2024-a4-primep (p)
  (and (natp p)
       (< 1 p)
       (putnam-2024-a4-no-divisor-from-p p 2)))

;; For BASE > 0, the first COUNT base-BASE digits of CODE form a list.
;; When COUNT = BASE and CODE ranges below BASE^BASE, these lists enumerate
;; every function from {0,...,BASE-1} to itself.
(defun putnam-2024-a4-decode-exponents (code base count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (mod code base)
          (putnam-2024-a4-decode-exponents
           (floor code base)
           base
           (- count 1)))))

(defun putnam-2024-a4-permutation-p (exponents maximum)
  (if (endp exponents)
      (equal exponents nil)
    (and (natp (car exponents))
         (<= (car exponents) maximum)
         (not (member-equal (car exponents) (cdr exponents)))
         (putnam-2024-a4-permutation-p
          (cdr exponents)
          maximum))))

(defun putnam-2024-a4-progression-p (p a r exponents)
  (if (and (consp exponents)
           (consp (cdr exponents)))
      (and
       (equal
        (mod
         (- (- (expt a (cadr exponents))
               (expt a (car exponents)))
            r)
         p)
        0)
       (putnam-2024-a4-progression-p
        p a r (cdr exponents)))
    t))

(defun putnam-2024-a4-rearrangement-code-p (p a r code)
  (let* ((maximum (- p 5))
         (base (+ maximum 1))
         (exponents
          (putnam-2024-a4-decode-exponents
           code base base)))
    (and
     (putnam-2024-a4-permutation-p exponents maximum)
     (putnam-2024-a4-progression-p p a r exponents))))

;; This finite search keeps the existentially quantified bijection internal.
;; A length-(p-4) duplicate-free list in 0..p-5 is exactly the restriction of
;; a source bijection e to that interval.
(defun putnam-2024-a4-rearrangement-through-p (p a r code)
  (declare (xargs :measure (nfix code)))
  (if (natp code)
      (or
       (putnam-2024-a4-rearrangement-code-p p a r code)
       (and
        (not (zp code))
        (putnam-2024-a4-rearrangement-through-p
         p a r (- code 1))))
    nil))

(defun putnam-2024-a4-a-r-code-p (p code)
  (let* ((r-count (- p 1))
         (a (floor code r-count))
         (r (+ 1 (mod code r-count)))
         (base (- p 4)))
    (putnam-2024-a4-rearrangement-through-p
     p a r (- (expt base base) 1))))

;; Divisibility of differences of powers modulo positive p depends only on
;; a modulo p. Thus searching a = 0,...,p-1 is equivalent to the source
;; existential over all integers a; r already lies in 1,...,p-1.
(defun putnam-2024-a4-a-r-through-p (p code)
  (declare (xargs :measure (nfix code)))
  (if (natp code)
      (or
       (putnam-2024-a4-a-r-code-p p code)
       (and
        (not (zp code))
        (putnam-2024-a4-a-r-through-p p (- code 1))))
    nil))

(defun putnam-2024-a4-qualifying-prime-p (p)
  (and
   (putnam-2024-a4-primep p)
   (< 5 p)
   (putnam-2024-a4-a-r-through-p
    p (- (* p (- p 1)) 1))))

(defun putnambench-putnam-2024-a4-statement (p)
  (implies
   (natp p)
   (equal
    (putnam-2024-a4-qualifying-prime-p p)
    (equal p 7))))

(value-triple :itpeval-statement-checked)
:q
