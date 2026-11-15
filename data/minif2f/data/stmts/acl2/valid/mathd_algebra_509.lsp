;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_509:
;; the principal real square root of
;; (5/sqrt(80) + sqrt(845)/9 + sqrt(45))/sqrt(5) is 13/6.
;; This file contains no proof.
;;
;; Every displayed radical and every intermediate value lies in Q(sqrt(5)).
;; A rational pair below gives an exact ordered-field representation, and a
;; nonnegative element is a principal square root exactly when its square is
;; the radicand. Thus the final predicate is bidirectionally equivalent to the
;; source equality over the reals, without replacing radicals by approximations.

(in-package "ACL2")

;; The dotted pair (a . b) represents a + b*sqrt(5).
(defun mathd-algebra-509-q5p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun mathd-algebra-509-q5 (a b)
  (cons a b))

(defun mathd-algebra-509-rational (q)
  (mathd-algebra-509-q5 q 0))

(defun mathd-algebra-509-sqrt5 ()
  (mathd-algebra-509-q5 0 1))

(defun mathd-algebra-509-add (x y)
  (mathd-algebra-509-q5
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun mathd-algebra-509-neg (x)
  (mathd-algebra-509-q5
   (- (car x))
   (- (cdr x))))

(defun mathd-algebra-509-mul (x y)
  (mathd-algebra-509-q5
   (+ (* (car x) (car y))
      (* 5 (cdr x) (cdr y)))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun mathd-algebra-509-inverse (x)
  (let* ((a (car x))
         (b (cdr x))
         (norm (- (* a a) (* 5 b b))))
    (mathd-algebra-509-q5
     (/ a norm)
     (/ (- b) norm))))

(defun mathd-algebra-509-div (x y)
  (mathd-algebra-509-mul
   x
   (mathd-algebra-509-inverse y)))

(defun mathd-algebra-509-square (x)
  (mathd-algebra-509-mul x x))

;; Exact nonnegativity for a + b*sqrt(5).
(defun mathd-algebra-509-nonnegativep (x)
  (and
   (mathd-algebra-509-q5p x)
   (let ((a (car x))
         (b (cdr x)))
     (cond ((< 0 b)
            (or (<= 0 a)
                (<= (* a a)
                    (* 5 b b))))
           ((< b 0)
            (and (<= 0 a)
                 (<= (* 5 b b)
                     (* a a))))
           (t (<= 0 a))))))

(defun mathd-algebra-509-principal-square-root-p (root radicand)
  (and (mathd-algebra-509-q5p root)
       (mathd-algebra-509-q5p radicand)
       (mathd-algebra-509-nonnegativep root)
       (equal (mathd-algebra-509-square root)
              radicand)))

(defun mathd-algebra-509-statement ()
  (let* ((five (mathd-algebra-509-rational 5))
         (sqrt5 (mathd-algebra-509-sqrt5))
         (sqrt80 (mathd-algebra-509-q5 0 4))
         (sqrt845 (mathd-algebra-509-q5 0 13))
         (sqrt45 (mathd-algebra-509-q5 0 3))
         (first-term
          (mathd-algebra-509-div
           five
           sqrt80))
         (second-term
          (mathd-algebra-509-div
           sqrt845
           (mathd-algebra-509-rational 9)))
         (numerator
          (mathd-algebra-509-add
           (mathd-algebra-509-add
            first-term
            second-term)
           sqrt45))
         (radicand
          (mathd-algebra-509-div
           numerator
           sqrt5))
         (target
          (mathd-algebra-509-rational (/ 13 6))))
    (and
     (mathd-algebra-509-principal-square-root-p
      sqrt5
      five)
     (mathd-algebra-509-principal-square-root-p
      sqrt80
      (mathd-algebra-509-rational 80))
     (mathd-algebra-509-principal-square-root-p
      sqrt845
      (mathd-algebra-509-rational 845))
     (mathd-algebra-509-principal-square-root-p
      sqrt45
      (mathd-algebra-509-rational 45))
     (mathd-algebra-509-principal-square-root-p
      target
      radicand))))

(value-triple :itpeval-statement-checked)
:q
