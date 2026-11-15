;; Statement-only formalization of miniF2F corpus artifact amc12a_2013_p8:
;; distinct nonzero real numbers x and y with x + 2/x = y + 2/y have
;; product 2. Reals are represented exactly by rational Cauchy names modulo
;; equality of their limits. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A regular rational Cauchy name represents its real limit. Every real has
;; such a name, so this completion encoding does not restrict the domain to
;; rational numbers.

(defun amc12a-2013-p8-positive-rational-p (value)
  (and (rationalp value)
       (< 0 value)))

(defun amc12a-2013-p8-real-value (name index)
  (apply$ name (list index)))

(defun-sk amc12a-2013-p8-rational-values-p (name)
  (forall (index)
    (implies
     (natp index)
     (rationalp
      (amc12a-2013-p8-real-value name index)))))

(defun-sk amc12a-2013-p8-regular-cauchy-p (name)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index))
     (<=
      (abs
       (-
        (amc12a-2013-p8-real-value name left-index)
        (amc12a-2013-p8-real-value name right-index)))
      (+
       (/ 1 (+ 1 left-index))
       (/ 1 (+ 1 right-index)))))))

(defun amc12a-2013-p8-real-name-p (name)
  (and
   (tamep-functionp name)
   (amc12a-2013-p8-rational-values-p name)
   (amc12a-2013-p8-regular-cauchy-p name)))

;; These pointwise rational sequences denote x, y, x + 2/x, y + 2/y,
;; x*y, and the constants 0 and 2. Division is total in ACL2, but for a
;; nonzero real name any zero-valued approximants occur only finitely often,
;; so their values do not affect the represented reciprocal.

(defun amc12a-2013-p8-expression-value
    (kind x y index)
  (let ((x-value
         (amc12a-2013-p8-real-value x index))
        (y-value
         (amc12a-2013-p8-real-value y index)))
    (cond
     ((equal kind :x)
      x-value)
     ((equal kind :y)
      y-value)
     ((equal kind :left-side)
      (+ x-value (/ 2 x-value)))
     ((equal kind :right-side)
      (+ y-value (/ 2 y-value)))
     ((equal kind :product)
      (* x-value y-value))
     ((equal kind :two)
      2)
     (t 0))))

;; Two displayed sequences represent the same real exactly when their
;; difference tends to zero. Positive rational radii form a neighborhood
;; basis, so these quantifiers state equality over the real completion.

(defun-sk amc12a-2013-p8-expression-distance-tail-p
    (left-kind right-kind x y margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (-
        (amc12a-2013-p8-expression-value
         left-kind x y index)
        (amc12a-2013-p8-expression-value
         right-kind x y index)))
      margin))))

(defun-sk amc12a-2013-p8-expression-distance-below-p
    (left-kind right-kind x y epsilon)
  (exists (margin cutoff)
    (and
     (amc12a-2013-p8-positive-rational-p margin)
     (< margin epsilon)
     (natp cutoff)
     (amc12a-2013-p8-expression-distance-tail-p
      left-kind right-kind x y margin cutoff))))

(defun-sk amc12a-2013-p8-expression-equal-p
    (left-kind right-kind x y)
  (forall (epsilon)
    (implies
     (amc12a-2013-p8-positive-rational-p epsilon)
     (amc12a-2013-p8-expression-distance-below-p
      left-kind right-kind x y epsilon))))

(defun-sk amc12a-2013-p8-statement ()
  (forall (x y)
    (implies
     (and
      (amc12a-2013-p8-real-name-p x)
      (amc12a-2013-p8-real-name-p y)
      (not
       (amc12a-2013-p8-expression-equal-p
        :x :zero x y))
      (not
       (amc12a-2013-p8-expression-equal-p
        :y :zero x y))
      (not
       (amc12a-2013-p8-expression-equal-p
        :x :y x y))
      (amc12a-2013-p8-expression-equal-p
       :left-side :right-side x y))
     (amc12a-2013-p8-expression-equal-p
      :product :two x y))))

(value-triple :itpeval-statement-checked)
:q
