;; Statement-only formalization of miniF2F artifact mathd_algebra_320:
;; positive natural numbers a, b, and c with c = 2 and a nonnegative real x
;; satisfying 2*x^2 = 4*x + 9 and x = (a + sqrt(b))/c have
;; a + b + c = 26. A pair (r . s) represents r + s*sqrt(b); the
;; representation hypothesis covers every satisfying real x. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-320-surdp (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun mathd-algebra-320-surd (r s)
  (cons r s))

(defun mathd-algebra-320-surd-rational (q)
  (mathd-algebra-320-surd q 0))

(defun mathd-algebra-320-surd-add (x y)
  (mathd-algebra-320-surd
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun mathd-algebra-320-surd-mul (x y b)
  (mathd-algebra-320-surd
   (+ (* (car x) (car y))
      (* b (cdr x) (cdr y)))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun mathd-algebra-320-surd-scale (q x)
  (mathd-algebra-320-surd
   (* q (car x))
   (* q (cdr x))))

;; Exact equality of r + s*sqrt(b), including the case when b is a square.
(defun mathd-algebra-320-surd-equal (x y b)
  (let ((r (- (car x) (car y)))
        (s (- (cdr x) (cdr y))))
    (or (and (equal s 0)
             (equal r 0))
        (and (not (equal s 0))
             (<= (* r s) 0)
             (equal (* r r)
                    (* b s s))))))

;; Exact nonnegativity of r + s*sqrt(b) for b >= 0.
(defun mathd-algebra-320-surd-nonnegative (x b)
  (let ((r (car x))
        (s (cdr x)))
    (cond ((equal s 0)
           (<= 0 r))
          ((< 0 s)
           (or (<= 0 r)
               (<= (* r r)
                   (* b s s))))
          (t
           (and (<= 0 r)
                (<= (* b s s)
                    (* r r)))))))

(defun mathd-algebra-320-statement (x a b c)
  (let* ((x-squared
          (mathd-algebra-320-surd-mul x x b))
         (quadratic-left
          (mathd-algebra-320-surd-scale 2 x-squared))
         (quadratic-right
          (mathd-algebra-320-surd-add
           (mathd-algebra-320-surd-scale 4 x)
           (mathd-algebra-320-surd-rational 9)))
         (represented-x
          (mathd-algebra-320-surd
           (/ a c)
           (/ 1 c))))
    (implies
     (and (mathd-algebra-320-surdp x)
          (natp a)
          (natp b)
          (natp c)
          (< 0 a)
          (< 0 b)
          (< 0 c)
          (mathd-algebra-320-surd-nonnegative x b)
          (mathd-algebra-320-surd-equal
           quadratic-left quadratic-right b)
          (mathd-algebra-320-surd-equal x represented-x b)
          (equal c 2))
     (equal (+ a b c) 26))))

(value-triple :itpeval-statement-checked)
:q
