;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/isqrt_Simple_isqrtqtvc: the simple integer square-root verification
;; condition, including initialization at zero and the universally quantified
;; loop preservation or exit specification. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun ntp4vc-isqrt-simple-square (value)
  (* value value))

(defun ntp4vc-isqrt-simple-spec-p (x result)
  (and
   (<= 0 result)
   (<=
    (ntp4vc-isqrt-simple-square result)
    x)
   (<
    x
    (ntp4vc-isqrt-simple-square
     (+ result 1)))))

;; Preserve the source universal quantifier over every integer loop counter.

(defun-sk ntp4vc-isqrt-simple-all-counts-p (x)
  (forall (count)
    (implies
     (integerp count)
     (implies
      (and
       (<= 0 count)
       (<=
        (ntp4vc-isqrt-simple-square count)
        x))
      (if
          (<=
           (ntp4vc-isqrt-simple-square
            (+ count 1))
           x)
          (and
           (and
            (<= 0 (- x count))
            (<
             (- x (+ count 1))
             (- x count)))
           (<= 0 (+ count 1))
           (<=
            (ntp4vc-isqrt-simple-square
             (+ count 1))
            x)
           (equal
            (+
             (ntp4vc-isqrt-simple-square
              (+ count 1))
             (+
              (* 2 (+ count 1))
              1))
            (ntp4vc-isqrt-simple-square
             (+ count 1 1))))
        (ntp4vc-isqrt-simple-spec-p
         x count))))))

(defun ntp4vc-pearl-isqrt-simple-isqrtqtvc-statement (x)
  (implies
   (and
    (integerp x)
    (<= 0 x))
   (and
    (<= 0 0)
    (<=
     (ntp4vc-isqrt-simple-square 0)
     x)
    (equal
     1
     (ntp4vc-isqrt-simple-square
      (+ 0 1)))
    (ntp4vc-isqrt-simple-all-counts-p
     x))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
