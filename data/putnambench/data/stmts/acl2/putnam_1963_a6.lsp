;; Statement-only formalization of PutnamBench corpus artifact putnam_1963_a6:
;; the midpoint relation determined by three chords of a real ellipse and
;; the intersections of their endpoint-joining lines. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar context below presents an arbitrary ordered field by tame
;; APPLY$ function objects. The resulting coordinate formula is universal
;; and quantifier-free in the ordered-field language. It is equivalent to
;; the source statement over the reals, and its validity over the reals is
;; equivalent to its validity over every ordered field: real closed fields
;; are elementarily equivalent, every ordered field embeds in a real closure,
;; and universal formulas are preserved by ordered subfields.
;;
;; If x and y are squared distances and r > 0, then
;;
;;   sqrt(x) + sqrt(y) = r
;;
;; is bidirectionally equivalent over the reals to
;;
;;   0 <= r^2 - x - y
;;   (r^2 - x - y)^2 = 4xy.
;;
;; Collinearity is the vanishing of the planar orientation determinant. For
;; collinear points, (P-A) dot (P-B) <= 0 is exactly membership in the closed
;; segment AB. With distinct endpoints, equality of two closed segments is
;; equality of their unordered endpoint pairs. Midpoints are expressed by
;; the coordinate equalities 2M = X + Y.

(defun putnam-1963-a6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1963-a6-unary-value (operation x)
  (apply$ operation (list x)))

(defun putnam-1963-a6-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk putnam-1963-a6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1963-a6-member-p carrier x)
      (putnam-1963-a6-member-p carrier y)
      (putnam-1963-a6-member-p carrier z))
     (and
      (putnam-1963-a6-member-p
       carrier
       (putnam-1963-a6-binary-value add x y))
      (putnam-1963-a6-member-p
       carrier
       (putnam-1963-a6-binary-value multiply x y))
      (putnam-1963-a6-member-p
       carrier
       (putnam-1963-a6-unary-value negate x))
      (implies
       (not (equal x zero))
       (putnam-1963-a6-member-p
        carrier
        (putnam-1963-a6-unary-value inverse x)))
      (equal
       (putnam-1963-a6-binary-value
        add
        (putnam-1963-a6-binary-value add x y)
        z)
       (putnam-1963-a6-binary-value
        add
        x
        (putnam-1963-a6-binary-value add y z)))
      (equal
       (putnam-1963-a6-binary-value add x y)
       (putnam-1963-a6-binary-value add y x))
      (equal
       (putnam-1963-a6-binary-value add x zero)
       x)
      (equal
       (putnam-1963-a6-binary-value
        add x (putnam-1963-a6-unary-value negate x))
       zero)
      (equal
       (putnam-1963-a6-binary-value
        multiply
        (putnam-1963-a6-binary-value multiply x y)
        z)
       (putnam-1963-a6-binary-value
        multiply
        x
        (putnam-1963-a6-binary-value multiply y z)))
      (equal
       (putnam-1963-a6-binary-value multiply x y)
       (putnam-1963-a6-binary-value multiply y x))
      (equal
       (putnam-1963-a6-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1963-a6-binary-value
         multiply
         x
         (putnam-1963-a6-unary-value inverse x))
        one))
      (equal
       (putnam-1963-a6-binary-value
        multiply
        x
        (putnam-1963-a6-binary-value add y z))
       (putnam-1963-a6-binary-value
        add
        (putnam-1963-a6-binary-value multiply x y)
        (putnam-1963-a6-binary-value multiply x z)))))))

(defun-sk putnam-1963-a6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (putnam-1963-a6-member-p carrier x)
      (putnam-1963-a6-member-p carrier y)
      (putnam-1963-a6-member-p carrier z))
     (and
      (not (putnam-1963-a6-binary-value less x x))
      (or
       (equal x y)
       (putnam-1963-a6-binary-value less x y)
       (putnam-1963-a6-binary-value less y x))
      (implies
       (and
        (putnam-1963-a6-binary-value less x y)
        (putnam-1963-a6-binary-value less y z))
       (putnam-1963-a6-binary-value less x z))
      (implies
       (putnam-1963-a6-binary-value less x y)
       (putnam-1963-a6-binary-value
        less
        (putnam-1963-a6-binary-value add x z)
        (putnam-1963-a6-binary-value add y z)))
      (implies
       (and
        (putnam-1963-a6-binary-value less zero x)
        (putnam-1963-a6-binary-value less zero y))
       (putnam-1963-a6-binary-value
        less
        zero
        (putnam-1963-a6-binary-value multiply x y)))))))

(defun putnam-1963-a6-ordered-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1963-a6-member-p carrier zero)
   (putnam-1963-a6-member-p carrier one)
   (not (equal zero one))
   (putnam-1963-a6-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1963-a6-order-laws-p
    carrier add multiply zero less)
   (putnam-1963-a6-binary-value less zero one)))

(defun putnam-1963-a6-r-carrier (context) (nth 0 context))
(defun putnam-1963-a6-r-zero (context) (nth 1 context))
(defun putnam-1963-a6-r-one (context) (nth 2 context))
(defun putnam-1963-a6-r-add (context) (nth 3 context))
(defun putnam-1963-a6-r-multiply (context) (nth 4 context))
(defun putnam-1963-a6-r-negate (context) (nth 5 context))
(defun putnam-1963-a6-r-inverse (context) (nth 6 context))
(defun putnam-1963-a6-r-less (context) (nth 7 context))

(defun putnam-1963-a6-context-p (context)
  (and
   (true-listp context)
   (equal (len context) 8)
   (putnam-1963-a6-ordered-field-p
    (putnam-1963-a6-r-carrier context)
    (putnam-1963-a6-r-add context)
    (putnam-1963-a6-r-multiply context)
    (putnam-1963-a6-r-negate context)
    (putnam-1963-a6-r-inverse context)
    (putnam-1963-a6-r-zero context)
    (putnam-1963-a6-r-one context)
    (putnam-1963-a6-r-less context))))

(defun putnam-1963-a6-scalar-p (context x)
  (putnam-1963-a6-member-p
   (putnam-1963-a6-r-carrier context) x))

(defun putnam-1963-a6-add (context x y)
  (putnam-1963-a6-binary-value
   (putnam-1963-a6-r-add context) x y))

(defun putnam-1963-a6-multiply (context x y)
  (putnam-1963-a6-binary-value
   (putnam-1963-a6-r-multiply context) x y))

(defun putnam-1963-a6-negate (context x)
  (putnam-1963-a6-unary-value
   (putnam-1963-a6-r-negate context) x))

(defun putnam-1963-a6-subtract (context x y)
  (putnam-1963-a6-add
   context x (putnam-1963-a6-negate context y)))

(defun putnam-1963-a6-less-p (context x y)
  (if
   (putnam-1963-a6-binary-value
    (putnam-1963-a6-r-less context) x y)
   t
   nil))

(defun putnam-1963-a6-less-equal-p (context x y)
  (not (putnam-1963-a6-less-p context y x)))

(defun putnam-1963-a6-square (context x)
  (putnam-1963-a6-multiply context x x))

(defun putnam-1963-a6-two (context)
  (putnam-1963-a6-add
   context
   (putnam-1963-a6-r-one context)
   (putnam-1963-a6-r-one context)))

(defun putnam-1963-a6-four (context)
  (putnam-1963-a6-square
   context (putnam-1963-a6-two context)))

(defun putnam-1963-a6-point-equal-p (left right)
  (and
   (equal (car left) (car right))
   (equal (cadr left) (cadr right))))

(defun putnam-1963-a6-distance-squared (context left right)
  (putnam-1963-a6-add
   context
   (putnam-1963-a6-square
    context
    (putnam-1963-a6-subtract
     context (car left) (car right)))
   (putnam-1963-a6-square
    context
    (putnam-1963-a6-subtract
     context (cadr left) (cadr right)))))

(defun putnam-1963-a6-orientation (context a b c)
  (putnam-1963-a6-subtract
   context
   (putnam-1963-a6-multiply
    context
    (putnam-1963-a6-subtract
     context (car b) (car a))
    (putnam-1963-a6-subtract
     context (cadr c) (cadr a)))
   (putnam-1963-a6-multiply
    context
    (putnam-1963-a6-subtract
     context (cadr b) (cadr a))
    (putnam-1963-a6-subtract
     context (car c) (car a)))))

(defun putnam-1963-a6-collinear-p (context a b c)
  (equal
   (putnam-1963-a6-orientation context a b c)
   (putnam-1963-a6-r-zero context)))

(defun putnam-1963-a6-closed-segment-p (context point a b)
  (and
   (putnam-1963-a6-collinear-p context point a b)
   (putnam-1963-a6-less-equal-p
    context
    (putnam-1963-a6-add
     context
     (putnam-1963-a6-multiply
      context
      (putnam-1963-a6-subtract
       context (car point) (car a))
      (putnam-1963-a6-subtract
       context (car point) (car b)))
     (putnam-1963-a6-multiply
      context
      (putnam-1963-a6-subtract
       context (cadr point) (cadr a))
      (putnam-1963-a6-subtract
       context (cadr point) (cadr b))))
    (putnam-1963-a6-r-zero context))))

(defun putnam-1963-a6-segments-equal-p (a b c d)
  (or
   (and
    (putnam-1963-a6-point-equal-p a c)
    (putnam-1963-a6-point-equal-p b d))
   (and
    (putnam-1963-a6-point-equal-p a d)
    (putnam-1963-a6-point-equal-p b c))))

(defun putnam-1963-a6-ellipse-point-p
    (context point f1 f2 r)
  (let* ((first-distance-squared
          (putnam-1963-a6-distance-squared
           context point f1))
         (second-distance-squared
          (putnam-1963-a6-distance-squared
           context point f2))
         (radius-squared
          (putnam-1963-a6-square context r))
         (ellipse-defect
          (putnam-1963-a6-subtract
           context
           (putnam-1963-a6-subtract
            context radius-squared first-distance-squared)
           second-distance-squared)))
    (and
     (putnam-1963-a6-less-equal-p
      context
      (putnam-1963-a6-r-zero context)
      ellipse-defect)
     (equal
      (putnam-1963-a6-square context ellipse-defect)
      (putnam-1963-a6-multiply
       context
       (putnam-1963-a6-four context)
       (putnam-1963-a6-multiply
        context
        first-distance-squared
        second-distance-squared))))))

(defun putnam-1963-a6-midpoint-p
    (context midpoint left right)
  (let ((two (putnam-1963-a6-two context)))
    (and
     (equal
      (putnam-1963-a6-multiply
       context two (car midpoint))
      (putnam-1963-a6-add
       context (car left) (car right)))
     (equal
      (putnam-1963-a6-multiply
       context two (cadr midpoint))
      (putnam-1963-a6-add
       context (cadr left) (cadr right))))))

(defun putnambench-putnam-1963-a6-statement
    (context
     f1-x f1-y f2-x f2-y
     u-x u-y v-x v-y
     a-x a-y b-x b-y
     c-x c-y d-x d-y
     p-x p-y q-x q-y
     m-x m-y r)
  (let* ((f1 (list f1-x f1-y))
         (f2 (list f2-x f2-y))
         (u (list u-x u-y))
         (v (list v-x v-y))
         (a (list a-x a-y))
         (b (list b-x b-y))
         (c (list c-x c-y))
         (d (list d-x d-y))
         (p (list p-x p-y))
         (q (list q-x q-y))
         (m (list m-x m-y)))
    (implies
     (and
      (putnam-1963-a6-context-p context)
      (putnam-1963-a6-scalar-p context f1-x)
      (putnam-1963-a6-scalar-p context f1-y)
      (putnam-1963-a6-scalar-p context f2-x)
      (putnam-1963-a6-scalar-p context f2-y)
      (putnam-1963-a6-scalar-p context u-x)
      (putnam-1963-a6-scalar-p context u-y)
      (putnam-1963-a6-scalar-p context v-x)
      (putnam-1963-a6-scalar-p context v-y)
      (putnam-1963-a6-scalar-p context a-x)
      (putnam-1963-a6-scalar-p context a-y)
      (putnam-1963-a6-scalar-p context b-x)
      (putnam-1963-a6-scalar-p context b-y)
      (putnam-1963-a6-scalar-p context c-x)
      (putnam-1963-a6-scalar-p context c-y)
      (putnam-1963-a6-scalar-p context d-x)
      (putnam-1963-a6-scalar-p context d-y)
      (putnam-1963-a6-scalar-p context p-x)
      (putnam-1963-a6-scalar-p context p-y)
      (putnam-1963-a6-scalar-p context q-x)
      (putnam-1963-a6-scalar-p context q-y)
      (putnam-1963-a6-scalar-p context m-x)
      (putnam-1963-a6-scalar-p context m-y)
      (putnam-1963-a6-scalar-p context r)
      (putnam-1963-a6-less-p
       context (putnam-1963-a6-r-zero context) r)
      (putnam-1963-a6-less-p
       context
       (putnam-1963-a6-distance-squared context f1 f2)
       (putnam-1963-a6-square context r))
      (putnam-1963-a6-ellipse-point-p context u f1 f2 r)
      (putnam-1963-a6-ellipse-point-p context v f1 f2 r)
      (not (putnam-1963-a6-point-equal-p u v))
      (putnam-1963-a6-ellipse-point-p context a f1 f2 r)
      (putnam-1963-a6-ellipse-point-p context b f1 f2 r)
      (not (putnam-1963-a6-point-equal-p a b))
      (putnam-1963-a6-ellipse-point-p context c f1 f2 r)
      (putnam-1963-a6-ellipse-point-p context d f1 f2 r)
      (not (putnam-1963-a6-point-equal-p c d))
      (not (putnam-1963-a6-point-equal-p a c))
      (not (putnam-1963-a6-point-equal-p b d))
      (putnam-1963-a6-midpoint-p context m u v)
      (not (putnam-1963-a6-segments-equal-p a b u v))
      (not (putnam-1963-a6-segments-equal-p c d u v))
      (not (putnam-1963-a6-segments-equal-p a b c d))
      (putnam-1963-a6-closed-segment-p context m a b)
      (putnam-1963-a6-closed-segment-p context m c d)
      (putnam-1963-a6-collinear-p context p a c)
      (putnam-1963-a6-collinear-p context p u v)
      (putnam-1963-a6-collinear-p context q b d)
      (putnam-1963-a6-collinear-p context q u v))
     (putnam-1963-a6-midpoint-p context m p q))))

(value-triple :itpeval-statement-checked)
:q
