;; Statement-only formalization of thousand-theorems corpus artifact Q472883,
;; "Quadratic reciprocity theorem": the Legendre form relates distinct odd
;; primes, and the Jacobi form relates all odd natural numbers by the usual
;; reciprocity sign (-1)^((a/2)*(b/2)), with natural-number division. This
;; file contains no proof.

(in-package "ACL2")

(defun q472883-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (q472883-no-divisor-from-p n (+ d 1)))
    t))

(defun q472883-primep (n)
  (and (natp n)
       (< 1 n)
       (q472883-no-divisor-from-p n 2)))

(defun q472883-quadratic-residue-search-p (a p x)
  (declare (xargs :measure (nfix (- p x))))
  (if (and (natp a)
           (natp p)
           (< 0 p)
           (natp x)
           (< x p))
      (or (equal (mod (* x x) p) (mod a p))
          (q472883-quadratic-residue-search-p a p (+ x 1)))
    nil))

(defun q472883-legendre (p a)
  (if (and (natp p)
           (natp a)
           (< 1 p))
      (cond ((equal (mod a p) 0) 0)
            ((q472883-quadratic-residue-search-p a p 0) 1)
            (t -1))
    0))

(defun q472883-smallest-divisor-from (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (if (equal (mod n d) 0)
          d
        (q472883-smallest-divisor-from n (+ d 1)))
    n))

(defun q472883-jacobi-factor-product (a b fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (and (natp a)
           (natp b)
           (< 1 b)
           (natp fuel)
           (< 0 fuel))
      (let ((p (q472883-smallest-divisor-from b 2)))
        (* (q472883-legendre p a)
           (q472883-jacobi-factor-product
            a (floor b p) (- fuel 1))))
    1))

(defun q472883-jacobi (a b)
  (if (and (natp a)
           (natp b))
      (q472883-jacobi-factor-product a b b)
    1))

(defun thousand-theorems-q472883-quadratic-reciprocity-statement (p q)
  (implies
   (and (natp p)
        (natp q)
        (q472883-primep p)
        (q472883-primep q)
        (not (equal p 2))
        (not (equal q 2))
        (not (equal p q)))
   (equal
    (* (q472883-legendre q p)
       (q472883-legendre p q))
    (expt -1
          (* (floor p 2)
             (floor q 2))))))

(defun thousand-theorems-q472883-jacobi-quadratic-reciprocity-statement
  (a b)
  (implies
   (and (natp a)
        (natp b)
        (equal (mod a 2) 1)
        (equal (mod b 2) 1))
   (equal
    (q472883-jacobi a b)
    (* (expt -1
             (* (floor a 2)
                (floor b 2)))
       (q472883-jacobi b a)))))

(value-triple :itpeval-statement-checked)
:q
