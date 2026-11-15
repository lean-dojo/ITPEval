;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/gcd_vc_sp_BinaryGcd_binary_gcdqtvc: the binary-gcd verification
;; condition for nonnegative integers, including recursive-call descent and
;; preservation of the greatest common divisor. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These are integer division truncated toward zero and its associated
;; remainder, matching the pinned Why3 integer division and modulo semantics.

(defun ntp4vc-binary-gcd-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun ntp4vc-binary-gcd-tmod (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (-
       numerator
       (*
        denominator
        (ntp4vc-binary-gcd-tdiv
         numerator denominator)))
    0))

;; Int.gcd is the natural-number gcd of the absolute values of its integer
;; arguments. The subtraction recursion below is an exact total ACL2
;; definition of that mathematical function.

(defun ntp4vc-binary-gcd-nat (left right)
  (declare
   (xargs :measure
          (+ (nfix left) (nfix right))))
  (if (and (natp left) (natp right))
      (cond
       ((equal left 0) right)
       ((equal right 0) left)
       ((< left right)
        (ntp4vc-binary-gcd-nat
         left (- right left)))
       (t
        (ntp4vc-binary-gcd-nat
         (- left right) right)))
    0))

(defun ntp4vc-binary-gcd (left right)
  (if (and (integerp left) (integerp right))
      (ntp4vc-binary-gcd-nat
       (abs left)
       (abs right))
    0))

;; This is the first conjunct of the source VC. It retains every explicit
;; nonzero-divisor condition and each recursive-call termination inequality.

(defun ntp4vc-binary-gcd-descent-vc-p (u v)
  (if (< u v)
      (and
       (or
        (and
         (<= 0 v)
         (< u v))
        (and
         (equal v u)
         (<= 0 u)
         (< v u)))
       (<= 0 v)
       (<= 0 u))
    (implies
     (not (equal v 0))
     (and
      (not (equal 2 0))
      (if
          (equal
           (ntp4vc-binary-gcd-tmod u 2)
           0)
          (and
           (not (equal 2 0))
           (if
               (equal
                (ntp4vc-binary-gcd-tmod v 2)
                0)
               (and
                (not (equal 2 0))
                (let ((o1
                       (ntp4vc-binary-gcd-tdiv
                        v 2)))
                  (and
                   (not (equal 2 0))
                   (let ((o2
                          (ntp4vc-binary-gcd-tdiv
                           u 2)))
                     (and
                      (or
                       (and
                        (<= 0 v)
                        (< o1 v))
                       (and
                        (equal v o1)
                        (<= 0 u)
                        (< o2 u)))
                      (<= 0 o2)
                      (<= 0 o1))))))
             (and
              (not (equal 2 0))
              (let ((o1
                     (ntp4vc-binary-gcd-tdiv
                      u 2)))
                (and
                 (and
                  (<= 0 u)
                  (< o1 u))
                 (<= 0 o1)
                 (<= 0 v))))))
        (and
         (not (equal 2 0))
         (if
             (equal
              (ntp4vc-binary-gcd-tmod v 2)
              0)
             (and
              (not (equal 2 0))
              (let ((o1
                     (ntp4vc-binary-gcd-tdiv
                      v 2)))
                (and
                 (and
                  (<= 0 v)
                  (< o1 v))
                 (<= 0 u)
                 (<= 0 o1))))
           (and
            (not (equal 2 0))
            (let ((o1
                   (ntp4vc-binary-gcd-tdiv
                    (- u v) 2)))
              (and
               (and
                (<= 0 u)
                (< o1 u))
               (<= 0 o1)
               (<= 0 v)))))))))))

;; This is exactly the conditional equation that supplies a possible result
;; of the binary-gcd recursion in the second conjunct of the source VC.

(defun ntp4vc-binary-gcd-result-premise-p
    (u v result)
  (if (< u v)
      (equal
       result
       (ntp4vc-binary-gcd v u))
    (if (equal v 0)
        (equal result u)
      (if
          (equal
           (ntp4vc-binary-gcd-tmod u 2)
           0)
          (if
              (equal
               (ntp4vc-binary-gcd-tmod v 2)
               0)
              (equal
               result
               (*
                2
                (ntp4vc-binary-gcd
                 (ntp4vc-binary-gcd-tdiv u 2)
                 (ntp4vc-binary-gcd-tdiv v 2))))
            (equal
             result
             (ntp4vc-binary-gcd
              (ntp4vc-binary-gcd-tdiv u 2)
              v)))
        (if
            (equal
             (ntp4vc-binary-gcd-tmod v 2)
             0)
            (equal
             result
             (ntp4vc-binary-gcd
              u
              (ntp4vc-binary-gcd-tdiv v 2)))
          (equal
           result
           (ntp4vc-binary-gcd
            (ntp4vc-binary-gcd-tdiv
             (- u v) 2)
            v)))))))

;; Preserve the source universal quantifier over every integer result.

(defun-sk ntp4vc-binary-gcd-all-results-p (u v)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (ntp4vc-binary-gcd-result-premise-p
       u v result)
      (equal
       result
       (ntp4vc-binary-gcd u v))))))

(defun
  ntp4vc-pearl-gcd-vc-sp-binarygcd-binary-gcdqtvc-statement
  (u v)
  (implies
   (and
    (integerp u)
    (integerp v)
    (<= 0 u)
    (<= 0 v))
   (and
    (ntp4vc-binary-gcd-descent-vc-p u v)
    (ntp4vc-binary-gcd-all-results-p u v))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
