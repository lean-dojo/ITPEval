;; Statement-only formalization of miniF2F artifact mathd_algebra_184:
;; positive real numbers a and b satisfying a^2 = 6*b and a^2 = 54/b have
;; a = 3*sqrt(2). The hypotheses force every satisfying real pair to lie in
;; Q(sqrt(2)), so dotted rational pairs give an exact encoding. The division
;; equation is cross-multiplied using the explicit positivity of b. This file
;; contains no proof.

(in-package "ACL2")

;; A dotted pair (r . s) represents the real number r + s*sqrt(2).
(defun mathd-algebra-184-q2p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun mathd-algebra-184-q2 (r s)
  (cons r s))

(defun mathd-algebra-184-rational (q)
  (mathd-algebra-184-q2 q 0))

(defun mathd-algebra-184-mul (x y)
  (mathd-algebra-184-q2
   (+ (* (car x) (car y))
      (* 2 (* (cdr x) (cdr y))))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun mathd-algebra-184-scale (q x)
  (mathd-algebra-184-q2
   (* q (car x))
   (* q (cdr x))))

;; Exact strict positivity for r + s*sqrt(2).
(defun mathd-algebra-184-positivep (x)
  (and
   (mathd-algebra-184-q2p x)
   (let ((r (car x))
         (s (cdr x)))
     (cond ((< 0 s)
            (or (<= 0 r)
                (< (* r r)
                   (* 2 (* s s)))))
           ((< s 0)
            (and (< 0 r)
                 (< (* 2 (* s s))
                    (* r r))))
           (t (< 0 r))))))

(defun mathd-algebra-184-statement (a b)
  (implies
   (and
    (mathd-algebra-184-q2p a)
    (mathd-algebra-184-q2p b)
    (mathd-algebra-184-positivep a)
    (mathd-algebra-184-positivep b)
    (equal
     (mathd-algebra-184-mul a a)
     (mathd-algebra-184-scale 6 b))
    (equal
     (mathd-algebra-184-mul
      (mathd-algebra-184-mul a a)
      b)
     (mathd-algebra-184-rational 54)))
   (equal a
          (mathd-algebra-184-q2 0 3))))

(value-triple :itpeval-statement-checked)
:q
