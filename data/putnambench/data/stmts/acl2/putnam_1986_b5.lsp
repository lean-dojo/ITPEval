;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b5:
;; the Vieta involution (x,y,z) -> (x,y,-z-xy) preserves
;; x^2+y^2+z^2+xyz but is not a permutation of signed coordinate
;; polynomials with zero or two minus signs. This file contains no proof.

(in-package "ACL2")

;; A term is (EX EY EZ COEFFICIENT), and a polynomial is a list of nonzero
;; terms in strictly increasing lexicographic exponent order. This is a
;; canonical sparse representation of a polynomial in X, Y, and Z.

(defun putnam-1986-b5-term-ex (term)
  (nth 0 term))

(defun putnam-1986-b5-term-ey (term)
  (nth 1 term))

(defun putnam-1986-b5-term-ez (term)
  (nth 2 term))

(defun putnam-1986-b5-term-coefficient (term)
  (nth 3 term))

(defun putnam-1986-b5-term-p (term)
  (and
   (true-listp term)
   (equal (len term) 4)
   (natp (putnam-1986-b5-term-ex term))
   (natp (putnam-1986-b5-term-ey term))
   (natp (putnam-1986-b5-term-ez term))
   (rationalp (putnam-1986-b5-term-coefficient term))
   (not (equal (putnam-1986-b5-term-coefficient term) 0))))

(defun putnam-1986-b5-same-exponents-p (left right)
  (and
   (equal (putnam-1986-b5-term-ex left)
          (putnam-1986-b5-term-ex right))
   (equal (putnam-1986-b5-term-ey left)
          (putnam-1986-b5-term-ey right))
   (equal (putnam-1986-b5-term-ez left)
          (putnam-1986-b5-term-ez right))))

(defun putnam-1986-b5-exponents-less-p (left right)
  (or
   (< (putnam-1986-b5-term-ex left)
      (putnam-1986-b5-term-ex right))
   (and
    (equal (putnam-1986-b5-term-ex left)
           (putnam-1986-b5-term-ex right))
    (or
     (< (putnam-1986-b5-term-ey left)
        (putnam-1986-b5-term-ey right))
     (and
      (equal (putnam-1986-b5-term-ey left)
             (putnam-1986-b5-term-ey right))
      (< (putnam-1986-b5-term-ez left)
         (putnam-1986-b5-term-ez right)))))))

(defun putnam-1986-b5-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (putnam-1986-b5-term-p (car polynomial))
       (or
        (endp (cdr polynomial))
        (and
         (putnam-1986-b5-term-p (cadr polynomial))
         (putnam-1986-b5-exponents-less-p
          (car polynomial)
          (cadr polynomial))))
       (putnam-1986-b5-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1986-b5-make-term-like (term coefficient)
  (list
   (putnam-1986-b5-term-ex term)
   (putnam-1986-b5-term-ey term)
   (putnam-1986-b5-term-ez term)
   coefficient))

(defun putnam-1986-b5-insert-term (term polynomial)
  (cond
   ((equal (putnam-1986-b5-term-coefficient term) 0)
    polynomial)
   ((endp polynomial)
    (list term))
   ((putnam-1986-b5-same-exponents-p term (car polynomial))
    (let ((coefficient
           (+ (putnam-1986-b5-term-coefficient term)
              (putnam-1986-b5-term-coefficient
               (car polynomial)))))
      (if (equal coefficient 0)
          (cdr polynomial)
        (cons
         (putnam-1986-b5-make-term-like term coefficient)
         (cdr polynomial)))))
   ((putnam-1986-b5-exponents-less-p term (car polynomial))
    (cons term polynomial))
   (t
    (cons
     (car polynomial)
     (putnam-1986-b5-insert-term term (cdr polynomial))))))

(defun putnam-1986-b5-polynomial-add (left right)
  (if (consp left)
      (putnam-1986-b5-insert-term
       (car left)
       (putnam-1986-b5-polynomial-add (cdr left) right))
    right))

(defun putnam-1986-b5-multiply-terms (left right)
  (list
   (+ (putnam-1986-b5-term-ex left)
      (putnam-1986-b5-term-ex right))
   (+ (putnam-1986-b5-term-ey left)
      (putnam-1986-b5-term-ey right))
   (+ (putnam-1986-b5-term-ez left)
      (putnam-1986-b5-term-ez right))
   (* (putnam-1986-b5-term-coefficient left)
      (putnam-1986-b5-term-coefficient right))))

(defun putnam-1986-b5-polynomial-times-term (polynomial term)
  (if (consp polynomial)
      (putnam-1986-b5-insert-term
       (putnam-1986-b5-multiply-terms (car polynomial) term)
       (putnam-1986-b5-polynomial-times-term
        (cdr polynomial) term))
    nil))

(defun putnam-1986-b5-polynomial-mul (left right)
  (if (consp left)
      (putnam-1986-b5-polynomial-add
       (putnam-1986-b5-polynomial-times-term right (car left))
       (putnam-1986-b5-polynomial-mul (cdr left) right))
    nil))

(defun putnam-1986-b5-polynomial-scale (coefficient polynomial)
  (if (consp polynomial)
      (let ((scaled
             (* coefficient
                (putnam-1986-b5-term-coefficient
                 (car polynomial)))))
        (if (equal scaled 0)
            (putnam-1986-b5-polynomial-scale
             coefficient (cdr polynomial))
          (cons
           (putnam-1986-b5-make-term-like
            (car polynomial) scaled)
           (putnam-1986-b5-polynomial-scale
            coefficient (cdr polynomial)))))
    nil))

(defun putnam-1986-b5-polynomial-square (polynomial)
  (putnam-1986-b5-polynomial-mul polynomial polynomial))

(defun putnam-1986-b5-f-polynomial (p q r)
  (putnam-1986-b5-polynomial-add
   (putnam-1986-b5-polynomial-square p)
   (putnam-1986-b5-polynomial-add
    (putnam-1986-b5-polynomial-square q)
    (putnam-1986-b5-polynomial-add
     (putnam-1986-b5-polynomial-square r)
     (putnam-1986-b5-polynomial-mul
      p
      (putnam-1986-b5-polynomial-mul q r))))))

(defun putnam-1986-b5-polynomial-coefficient
    (ex ey ez polynomial)
  (if (consp polynomial)
      (if (and
           (equal ex
                  (putnam-1986-b5-term-ex (car polynomial)))
           (equal ey
                  (putnam-1986-b5-term-ey (car polynomial)))
           (equal ez
                  (putnam-1986-b5-term-ez (car polynomial))))
          (putnam-1986-b5-term-coefficient (car polynomial))
        (putnam-1986-b5-polynomial-coefficient
         ex ey ez (cdr polynomial)))
    0))

(defun putnam-1986-b5-x-polynomial ()
  (list (list 1 0 0 1)))

(defun putnam-1986-b5-y-polynomial ()
  (list (list 0 1 0 1)))

(defun putnam-1986-b5-z-polynomial ()
  (list (list 0 0 1 1)))

(defun putnam-1986-b5-polynomial-set-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (putnam-1986-b5-polynomial-set-subset-p
        (cdr left) right))
    t))

(defun putnam-1986-b5-polynomial-set-equal-p (left right)
  (and
   (putnam-1986-b5-polynomial-set-subset-p left right)
   (putnam-1986-b5-polynomial-set-subset-p right left)))

(defun putnam-1986-b5-permitted-polynomial-set-p (candidate)
  (let* ((x (putnam-1986-b5-x-polynomial))
         (y (putnam-1986-b5-y-polynomial))
         (z (putnam-1986-b5-z-polynomial))
         (minus-x (putnam-1986-b5-polynomial-scale -1 x))
         (minus-y (putnam-1986-b5-polynomial-scale -1 y))
         (minus-z (putnam-1986-b5-polynomial-scale -1 z)))
    (or
     (putnam-1986-b5-polynomial-set-equal-p
      candidate (list x y z))
     (putnam-1986-b5-polynomial-set-equal-p
      candidate (list x minus-y minus-z))
     (putnam-1986-b5-polynomial-set-equal-p
      candidate (list minus-x y minus-z))
     (putnam-1986-b5-polynomial-set-equal-p
      candidate (list minus-x minus-y z)))))

;; Equality of sparse polynomials is checked coefficientwise. Since these
;; rational-coefficient polynomials canonically embed into R[X,Y,Z], this
;; states the existence of a real-polynomial counterexample without selecting
;; a particular witness in the statement.
(defun-sk putnam-1986-b5-preserves-f-p (p q r)
  (forall (ex ey ez)
    (implies
     (and (natp ex) (natp ey) (natp ez))
     (let* ((x (putnam-1986-b5-x-polynomial))
            (y (putnam-1986-b5-y-polynomial))
            (z (putnam-1986-b5-z-polynomial))
            (original (putnam-1986-b5-f-polynomial x y z))
            (transformed (putnam-1986-b5-f-polynomial p q r)))
       (equal
        (putnam-1986-b5-polynomial-coefficient
         ex ey ez transformed)
        (putnam-1986-b5-polynomial-coefficient
         ex ey ez original))))))

(defun-sk putnam-1986-b5-counterexample-exists-p ()
  (exists (p q r)
    (and
     (putnam-1986-b5-polynomial-p p)
     (putnam-1986-b5-polynomial-p q)
     (putnam-1986-b5-polynomial-p r)
     (putnam-1986-b5-preserves-f-p p q r)
     (not
      (putnam-1986-b5-permitted-polynomial-set-p
       (list p q r))))))

;; The source answer is False, equivalently the proposed universal
;; classification has a counterexample.
(defun putnambench-putnam-1986-b5-statement ()
  (putnam-1986-b5-counterexample-exists-p))

(value-triple :itpeval-statement-checked)
:q
