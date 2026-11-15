;; Statement-only formalization of Hundred Theorems artifact
;; hundred-theorems__acl2__060, "Bézout's Theorem": for every pair of
;; integers x and y, explicitly computed integer coefficients u and v satisfy
;; u*x + v*y = gcd(|x|, |y|). This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-060-integer-abs (z)
  (if (integerp z)
      (if (< z 0)
          (- z)
        z)
    0))

(defun hundred-theorems-060-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (hundred-theorems-060-gcd a (- b a)))
            (t
             (hundred-theorems-060-gcd (- a b) b)))
    0))

(defun hundred-theorems-060-bezout-coefficients (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0)
             (cons 0 1))
            ((equal b 0)
             (cons 1 0))
            ((< a b)
             (let* ((coefficients
                     (hundred-theorems-060-bezout-coefficients
                      a (- b a)))
                    (u (car coefficients))
                    (v (cdr coefficients)))
               (cons (- u v) v)))
            (t
             (let* ((coefficients
                     (hundred-theorems-060-bezout-coefficients
                      (- a b) b))
                    (u (car coefficients))
                    (v (cdr coefficients)))
               (cons u (- v u)))))
    (cons 0 0)))

(defun hundred-theorems-060-sign (z)
  (if (and (integerp z)
           (< z 0))
      -1
    1))

(defun hundred-theorems-060-bezouts-theorem-statement (x y)
  (implies
   (and (integerp x)
        (integerp y))
   (let* ((absolute-x
           (hundred-theorems-060-integer-abs x))
          (absolute-y
           (hundred-theorems-060-integer-abs y))
          (coefficients
           (hundred-theorems-060-bezout-coefficients
            absolute-x absolute-y))
          (u (* (hundred-theorems-060-sign x)
                (car coefficients)))
          (v (* (hundred-theorems-060-sign y)
                (cdr coefficients))))
     (and (integerp u)
          (integerp v)
          (equal (+ (* u x) (* v y))
                 (hundred-theorems-060-gcd
                  absolute-x absolute-y))))))

(value-triple :itpeval-statement-checked)
:q
