;; Statement-only formalization of miniF2F artifact
;; algebra_others_exirrpowirrrat: there exist irrational real numbers a and b
;; whose real power a^b is rational. ACL2 reifies the standard case split on
;; whether sqrt(2)^sqrt(2) is rational and uses explicit witness parameters.
;; This file contains no proof.

(in-package "ACL2")

(defun algebra-others-exirrpowirrrat-rational (q)
  (list :rational q))

(defun algebra-others-exirrpowirrrat-sqrt-two ()
  (list :positive-square-root 2))

(defun algebra-others-exirrpowirrrat-sqrt-two-power ()
  (list :real-power
        (algebra-others-exirrpowirrrat-sqrt-two)
        (algebra-others-exirrpowirrrat-sqrt-two)))

(defun algebra-others-exirrpowirrrat-rational-expression-p (x)
  (and (true-listp x)
       (equal (len x) 2)
       (equal (car x) :rational)
       (rationalp (cadr x))))

(defun algebra-others-exirrpowirrrat-real-expression-p (x)
  (or (algebra-others-exirrpowirrrat-rational-expression-p x)
      (equal x
             (algebra-others-exirrpowirrrat-sqrt-two))
      (equal x
             (algebra-others-exirrpowirrrat-sqrt-two-power))))

(defun algebra-others-exirrpowirrrat-rational-p
    (x sqrt-two-power-is-rational)
  (and
   (algebra-others-exirrpowirrrat-real-expression-p x)
   (or (algebra-others-exirrpowirrrat-rational-expression-p x)
       (and
        (equal sqrt-two-power-is-rational t)
        (equal x
               (algebra-others-exirrpowirrrat-sqrt-two-power))))))

(defun algebra-others-exirrpowirrrat-irrational-p
    (x sqrt-two-power-is-rational)
  (and
   (algebra-others-exirrpowirrrat-real-expression-p x)
   (not
    (algebra-others-exirrpowirrrat-rational-p
     x sqrt-two-power-is-rational))))

;; These are the two real-power identities used by the standard case split:
;; sqrt(2)^sqrt(2) is the intermediate value, and raising that value to
;; sqrt(2) gives 2.
(defun algebra-others-exirrpowirrrat-real-power-p (base exponent result)
  (and
   (algebra-others-exirrpowirrrat-real-expression-p base)
   (algebra-others-exirrpowirrrat-real-expression-p exponent)
   (algebra-others-exirrpowirrrat-real-expression-p result)
   (or
    (and
     (equal base
            (algebra-others-exirrpowirrrat-sqrt-two))
     (equal exponent
            (algebra-others-exirrpowirrrat-sqrt-two))
     (equal result
            (algebra-others-exirrpowirrrat-sqrt-two-power)))
    (and
     (equal base
            (algebra-others-exirrpowirrrat-sqrt-two-power))
     (equal exponent
            (algebra-others-exirrpowirrrat-sqrt-two))
     (equal result
            (algebra-others-exirrpowirrrat-rational 2))))))

(defun algebra-others-exirrpowirrrat-statement
    (sqrt-two-power-is-rational a b a-to-b)
  (and
   (or (equal sqrt-two-power-is-rational t)
       (equal sqrt-two-power-is-rational nil))
   (algebra-others-exirrpowirrrat-real-expression-p a)
   (algebra-others-exirrpowirrrat-real-expression-p b)
   (algebra-others-exirrpowirrrat-real-expression-p a-to-b)
   (if (equal sqrt-two-power-is-rational t)
       (and
        (equal a
               (algebra-others-exirrpowirrrat-sqrt-two))
        (equal b
               (algebra-others-exirrpowirrrat-sqrt-two))
        (equal a-to-b
               (algebra-others-exirrpowirrrat-sqrt-two-power)))
     (and
      (equal a
             (algebra-others-exirrpowirrrat-sqrt-two-power))
      (equal b
             (algebra-others-exirrpowirrrat-sqrt-two))
      (equal a-to-b
             (algebra-others-exirrpowirrrat-rational 2))))
   (algebra-others-exirrpowirrrat-irrational-p
    a sqrt-two-power-is-rational)
   (algebra-others-exirrpowirrrat-irrational-p
    b sqrt-two-power-is-rational)
   (algebra-others-exirrpowirrrat-real-power-p a b a-to-b)
   (algebra-others-exirrpowirrrat-rational-p
    a-to-b sqrt-two-power-is-rational)))

(value-triple :itpeval-statement-checked)
:q
