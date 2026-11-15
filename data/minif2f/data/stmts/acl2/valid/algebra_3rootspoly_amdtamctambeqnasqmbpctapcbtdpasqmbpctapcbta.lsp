;; Statement-only formalization of miniF2F corpus artifact
;; algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
;; for all complex a, b, c, and d, (a-d)(a-c)(a-b) equals
;; -(a^2-(b+c)a+cb)d + (a^2-(b+c)a+cb)a. The universal four-variable
;; complex-polynomial identity is encoded as equality of complete
;; coefficients, with exponent tuple (i_a,i_b,i_c,i_d) stored at index
;; i_a + 4*i_b + 16*i_c + 64*i_d. All variable degrees are below 4, so
;; this indexing is injective; polynomial extensionality makes the encoding
;; bidirectionally equivalent to the source statement. This file contains no
;; proof.

(in-package "ACL2")

(defun algebra-3rootspoly-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (algebra-3rootspoly-polynomial-add
           (cdr left) (cdr right))))))

(defun algebra-3rootspoly-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (algebra-3rootspoly-polynomial-scale
           scalar (cdr polynomial)))))

(defun algebra-3rootspoly-polynomial-mul (left right)
  (if (endp left)
      nil
    (algebra-3rootspoly-polynomial-add
     (algebra-3rootspoly-polynomial-scale
      (car left) right)
     (cons
      0
      (algebra-3rootspoly-polynomial-mul
       (cdr left) right)))))

(defun algebra-3rootspoly-monomial (degree)
  (if (zp degree)
      (list 1)
    (cons 0
          (algebra-3rootspoly-monomial (1- degree)))))

(defun
 algebra-3rootspoly-amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta-statement
 ()
  (let* ((a-polynomial (algebra-3rootspoly-monomial 1))
         (b-polynomial (algebra-3rootspoly-monomial 4))
         (c-polynomial (algebra-3rootspoly-monomial 16))
         (d-polynomial (algebra-3rootspoly-monomial 64))
         (quadratic-polynomial
          (algebra-3rootspoly-polynomial-add
           (algebra-3rootspoly-polynomial-add
            (algebra-3rootspoly-polynomial-mul
             a-polynomial a-polynomial)
            (algebra-3rootspoly-polynomial-scale
             -1
             (algebra-3rootspoly-polynomial-mul
              (algebra-3rootspoly-polynomial-add
               b-polynomial c-polynomial)
              a-polynomial)))
           (algebra-3rootspoly-polynomial-mul
            c-polynomial b-polynomial))))
    (equal
     (algebra-3rootspoly-polynomial-mul
      (algebra-3rootspoly-polynomial-mul
       (algebra-3rootspoly-polynomial-add
        a-polynomial
        (algebra-3rootspoly-polynomial-scale -1 d-polynomial))
       (algebra-3rootspoly-polynomial-add
        a-polynomial
        (algebra-3rootspoly-polynomial-scale -1 c-polynomial)))
      (algebra-3rootspoly-polynomial-add
       a-polynomial
       (algebra-3rootspoly-polynomial-scale -1 b-polynomial)))
     (algebra-3rootspoly-polynomial-add
      (algebra-3rootspoly-polynomial-scale
       -1
       (algebra-3rootspoly-polynomial-mul
        quadratic-polynomial d-polynomial))
      (algebra-3rootspoly-polynomial-mul
       quadratic-polynomial a-polynomial)))))

(value-triple :itpeval-statement-checked)
:q
