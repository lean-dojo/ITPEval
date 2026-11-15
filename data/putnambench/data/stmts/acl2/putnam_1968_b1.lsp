;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1968_b1: for finite-valued integer random variables, the probability
;; that their minimum equals k is P(X = k) + P(Y = k) - P(max(X,Y) = k).
;; This file contains no proof.

(in-package "ACL2")

;; The predicate below is universal over integer x, y, and k. Its equality is
;; the pointwise identity between the four event indicators in the source.
;; Integrating that identity against any probability measure gives the source
;; conclusion for arbitrary measurable finite-valued X and Y. Conversely, the
;; source theorem applied to a one-point probability space with constant
;; values x and y gives this identity. This is therefore a bidirectionally
;; equivalent encoding and does not represent real probabilities by ACL2
;; rationals.

(defun putnam-1968-b1-indicator (condition)
  (if condition 1 0))

(defun putnam-1968-b1-minimum (x y)
  (if (<= x y) x y))

(defun putnam-1968-b1-maximum (x y)
  (if (<= x y) y x))

(defun putnambench-putnam-1968-b1-statement (x y k)
  (implies
   (and (integerp x)
        (integerp y)
        (integerp k))
   (equal
    (putnam-1968-b1-indicator
     (equal (putnam-1968-b1-minimum x y) k))
    (-
     (+ (putnam-1968-b1-indicator (equal x k))
        (putnam-1968-b1-indicator (equal y k)))
     (putnam-1968-b1-indicator
      (equal (putnam-1968-b1-maximum x y) k))))))

(value-triple :itpeval-statement-checked)
:q
