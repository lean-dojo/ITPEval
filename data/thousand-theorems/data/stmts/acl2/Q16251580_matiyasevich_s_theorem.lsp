;; Statement-only formalization of thousand-theorems corpus artifact Q16251580,
;; "Matiyasevich's theorem": membership in the Pell-recursive sequence is
;; characterized by Davis's natural-number Diophantine system of equations,
;; congruences, and divisibility conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The Pell pair uses the source recursion with natural-number subtraction.

(defun q16251580-nat-sub (left right)
  (nfix (- left right)))

(defun q16251580-pell-pair (a n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons 1 0)
    (let* ((previous
            (q16251580-pell-pair a (- n 1)))
           (previous-x (car previous))
           (previous-y (cdr previous))
           (d (q16251580-nat-sub (* a a) 1)))
      (cons
       (+ (* previous-x a)
          (* d previous-y))
       (+ previous-x
          (* previous-y a))))))

(defun q16251580-pell-x (a n)
  (car (q16251580-pell-pair a n)))

(defun q16251580-pell-y (a n)
  (cdr (q16251580-pell-pair a n)))

(defun q16251580-nat-modeq-p (left right modulus)
  (and
   (natp left)
   (natp right)
   (natp modulus)
   (if (zp modulus)
       (equal left right)
     (equal (mod left modulus)
            (mod right modulus)))))

(defun q16251580-nat-divides-p (divisor value)
  (and
   (natp divisor)
   (natp value)
   (if (zp divisor)
       (equal value 0)
     (equal (mod value divisor) 0))))

;; This is the source's internal existential quantifier over natural
;; u, v, s, tt, and b; TT represents the source witness named t.

(defun-sk q16251580-witness-exists-p (a k x y)
  (exists (u v s tt b)
    (and
     (natp u)
     (natp v)
     (natp s)
     (natp tt)
     (natp b)
     (equal
      (q16251580-nat-sub
       (* x x)
       (* (q16251580-nat-sub (* a a) 1)
          (* y y)))
      1)
     (equal
      (q16251580-nat-sub
       (* u u)
       (* (q16251580-nat-sub (* a a) 1)
          (* v v)))
      1)
     (equal
      (q16251580-nat-sub
       (* s s)
       (* (q16251580-nat-sub (* b b) 1)
          (* tt tt)))
      1)
     (< 1 b)
     (q16251580-nat-modeq-p b 1 (* 4 y))
     (q16251580-nat-modeq-p b a u)
     (< 0 v)
     (q16251580-nat-divides-p (* y y) v)
     (q16251580-nat-modeq-p s x u)
     (q16251580-nat-modeq-p tt k (* 4 y)))))

(defun thousand-theorems-q16251580-matiyasevich-s-theorem-statement
    (a k x y)
  (implies
   (and
    (natp a)
    (natp k)
    (natp x)
    (natp y))
   (iff
    (and
     (< 1 a)
     (equal (q16251580-pell-x a k) x)
     (equal (q16251580-pell-y a k) y))
    (and
     (< 1 a)
     (<= k y)
     (or
      (and
       (equal x 1)
       (equal y 0))
      (q16251580-witness-exists-p a k x y))))))

(value-triple :itpeval-statement-checked)
:q
