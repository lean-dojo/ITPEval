;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b2:
;; the complex difference triples arising from the given symmetric quadratic
;; equations are exactly four specified triples. This file contains no proof.

(in-package "ACL2")

;; Write a = x-y, b = y-z, and c = z-x. Then c = -(a+b), and subtracting
;; consecutive source equations gives
;;
;;   a(a+2b-1) = 0 and b(-2a-b-1) = 0.
;;
;; Conversely, these three equations give source witnesses x=a+b, y=b, z=0,
;; so this eliminates the source's internal existential quantifier in both
;; directions.
;;
;; ACL2 numbers are Gaussian rationals rather than arbitrary complex numbers.
;; This does not narrow this particular statement. Over the complex numbers,
;; the two product equations split into a=0 or a+2b=1, and b=0 or
;; 2a+b=-1. The four cases force (a,b,c) respectively to be
;; (0,0,0), (0,-1,1), (1,0,-1), or (-1,1,0). Thus every possible complex
;; output triple already has integer coordinates. Conversely, Gaussian
;; rationals embed in the complex numbers and the displayed witnesses realize
;; every target-side equation triple. Hence universal closure of the
;; componentwise ACL2 predicate is bidirectionally equivalent to equality of
;; the two source sets over all complex triples.

(defun putnam-1986-b2-listed-solution-p (a b c)
  (or (and (equal a 0)
           (equal b 0)
           (equal c 0))
      (and (equal a 0)
           (equal b -1)
           (equal c 1))
      (and (equal a 1)
           (equal b 0)
           (equal c -1))
      (and (equal a -1)
           (equal b 1)
           (equal c 0))))

(defun putnam-1986-b2-difference-equations-p (a b c)
  (and (equal c (- (+ a b)))
       (equal (* a (- (+ a (* 2 b)) 1)) 0)
       (equal (* b (- (- (+ (* 2 a) b)) 1)) 0)))

(defun putnambench-putnam-1986-b2-statement (a b c)
  (implies
   (and (acl2-numberp a)
        (acl2-numberp b)
        (acl2-numberp c))
   (iff (putnam-1986-b2-listed-solution-p a b c)
        (putnam-1986-b2-difference-equations-p a b c))))

(value-triple :itpeval-statement-checked)
:q
