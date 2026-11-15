;; Statement-only formalization of miniF2F corpus artifact aime_1990_p2:
;; the difference of the real 3/2 powers of 52 + 6*sqrt(43) and
;; 52 - 6*sqrt(43) is 828. ACL2 represents the values exactly in
;; Q(sqrt(43)); each base is the square of its displayed positive square
;; root, so its 3/2 power is that root cubed. This file contains no proof.

(in-package "ACL2")

;; A dotted pair (a . b) represents the real number a + b*sqrt(43).
(defun aime-1990-p2-q43p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun aime-1990-p2-q43 (a b)
  (cons a b))

(defun aime-1990-p2-rational (q)
  (aime-1990-p2-q43 q 0))

(defun aime-1990-p2-sqrt43 ()
  (aime-1990-p2-q43 0 1))

(defun aime-1990-p2-add (x y)
  (aime-1990-p2-q43
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun aime-1990-p2-neg (x)
  (aime-1990-p2-q43
   (- (car x))
   (- (cdr x))))

(defun aime-1990-p2-sub (x y)
  (aime-1990-p2-add x (aime-1990-p2-neg y)))

(defun aime-1990-p2-mul (x y)
  (aime-1990-p2-q43
   (+ (* (car x) (car y))
      (* 43 (* (cdr x) (cdr y))))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun aime-1990-p2-scale (q x)
  (aime-1990-p2-q43
   (* q (car x))
   (* q (cdr x))))

(defun aime-1990-p2-square (x)
  (aime-1990-p2-mul x x))

(defun aime-1990-p2-cube (x)
  (aime-1990-p2-mul
   (aime-1990-p2-square x)
   x))

;; Exact nonnegativity in Q(sqrt(43)).
(defun aime-1990-p2-nonnegativep (x)
  (and
   (aime-1990-p2-q43p x)
   (let ((a (car x))
         (b (cdr x)))
     (cond ((< 0 b)
            (or (<= 0 a)
                (<= (* a a)
                    (* 43 (* b b)))))
           ((< b 0)
            (and (<= 0 a)
                 (<= (* 43 (* b b))
                     (* a a))))
           (t (<= 0 a))))))

(defun aime-1990-p2-positivep (x)
  (and
   (aime-1990-p2-nonnegativep x)
   (not (equal x (aime-1990-p2-rational 0)))))

(defun aime-1990-p2-principal-square-root-p (root base)
  (and
   (aime-1990-p2-q43p root)
   (aime-1990-p2-q43p base)
   (aime-1990-p2-positivep root)
   (equal (aime-1990-p2-square root)
          base)))

;; For a positive base with principal square root r,
;; base^(3/2) = (sqrt(base))^3 = r^3.
(defun aime-1990-p2-rpow-three-halves (base principal-root)
  (if (aime-1990-p2-principal-square-root-p principal-root base)
      (aime-1990-p2-cube principal-root)
    (aime-1990-p2-rational 0)))

(defun aime-1990-p2-statement ()
  (let* ((sqrt43
          (aime-1990-p2-sqrt43))
         (six-sqrt43
          (aime-1990-p2-scale 6 sqrt43))
         (plus-base
          (aime-1990-p2-add
           (aime-1990-p2-rational 52)
           six-sqrt43))
         (minus-base
          (aime-1990-p2-sub
           (aime-1990-p2-rational 52)
           six-sqrt43))
         (plus-root
          (aime-1990-p2-add
           sqrt43
           (aime-1990-p2-rational 3)))
         (minus-root
          (aime-1990-p2-sub
           sqrt43
           (aime-1990-p2-rational 3))))
    (equal
     (aime-1990-p2-sub
      (aime-1990-p2-rpow-three-halves plus-base plus-root)
      (aime-1990-p2-rpow-three-halves minus-base minus-root))
     (aime-1990-p2-rational 828))))

(value-triple :itpeval-statement-checked)
:q
