;; Statement-only formalization of ntp4vc corpus artifact
;; pearl/multiprecision/sub_Sub_wmpn_subqtvc: the verification condition
;; for multiprecision subtraction with borrow propagation and limb copying.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove proof-builder observation))

(defun subvc-radix ()
  18446744073709551616)

(defun subvc-bv32-p (x)
  (and (integerp x)
       (<= 0 x)
       (< x 4294967296)))

(defun subvc-bv64-p (x)
  (and (integerp x)
       (<= 0 x)
       (< x (subvc-radix))))

(defun subvc-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun subvc-int32-bounds-p (x)
  (and (integerp x)
       (<= -2147483648 x)
       (< x 2147483648)))

(defun subvc-ipow (base exponent)
  (expt base (nfix exponent)))

(defun subvc-bv64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (subvc-bv64-p (car xs))
         (subvc-bv64-list-p (cdr xs)))))

; A pointer is (tag data offset min max writable zone).
(defun subvc-ptr-p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (nth 0 p) :subvc-ptr)
       (subvc-bv64-list-p (nth 1 p))
       (integerp (nth 2 p))
       (integerp (nth 3 p))
       (integerp (nth 4 p))
       (booleanp (nth 5 p))))

(defun subvc-ptr-data (p)
  (nth 1 p))

(defun subvc-ptr-offset (p)
  (nth 2 p))

(defun subvc-ptr-min (p)
  (nth 3 p))

(defun subvc-ptr-max (p)
  (nth 4 p))

(defun subvc-ptr-writable (p)
  (nth 5 p))

(defun subvc-ptr-zone (p)
  (nth 6 p))

(defun subvc-pelt (p index)
  (let ((value (nth (nfix index) (subvc-ptr-data p))))
    (if (subvc-bv64-p value)
        value
      0)))

(defun subvc-valid-p (p size)
  (and (subvc-int32-bounds-p size)
       (<= 0 size)
       (<= 0 (subvc-ptr-min p))
       (<= (subvc-ptr-min p)
           (subvc-ptr-offset p))
       (<= (+ (subvc-ptr-offset p) size)
           (subvc-ptr-max p))
       (<= (subvc-ptr-max p)
           (len (subvc-ptr-data p)))))

(defun subvc-bounds-p (p displacement)
  (and (<= (subvc-ptr-min p)
           (+ (subvc-ptr-offset p) displacement))
       (< (+ (subvc-ptr-offset p) displacement)
          (subvc-ptr-max p))))

(defun subvc-value-sub (p offset size)
  (declare (xargs :measure (nfix size)))
  (if (zp size)
      0
    (+ (subvc-pelt p offset)
       (* (subvc-radix)
          (subvc-value-sub p (+ offset 1) (- size 1))))))

(defun subvc-value (p size)
  (subvc-value-sub p (subvc-ptr-offset p) size))

(defun-sk subvc-pelts-equal-p (left right)
  (forall (index)
    (implies (integerp index)
             (equal (subvc-pelt left index)
                    (subvc-pelt right index)))))

(defun-sk subvc-map-eq-sub-p (current original lower upper)
  (forall (index)
    (implies (and (integerp index)
                  (<= lower index)
                  (< index upper))
             (equal (subvc-pelt current index)
                    (subvc-pelt original index)))))

(defun-sk subvc-outside-unchanged-p (current original size)
  (forall (index)
    (implies (and (integerp index)
                  (or (< index (subvc-ptr-offset current))
                      (<= (+ (subvc-ptr-offset current) size)
                          index)))
             (equal (subvc-pelt current index)
                    (subvc-pelt original index)))))

(defun-sk subvc-updated-p (new old index value)
  (forall (position)
    (implies (integerp position)
             (equal (subvc-pelt new position)
                    (if (equal position index)
                        value
                      (subvc-pelt old position))))))

(defun subvc-same-shape-p (new old)
  (and (equal (len (subvc-ptr-data new))
              (len (subvc-ptr-data old)))
       (equal (subvc-ptr-offset new)
              (subvc-ptr-offset old))
       (equal (subvc-ptr-min new)
              (subvc-ptr-min old))
       (equal (subvc-ptr-max new)
              (subvc-ptr-max old))
       (equal (subvc-ptr-writable new)
              (subvc-ptr-writable old))
       (equal (subvc-ptr-zone new)
              (subvc-ptr-zone old))))

(defun subvc-transition-p (ynew xnew rnew yold xold rold)
  (and (subvc-ptr-p ynew)
       (subvc-ptr-p xnew)
       (subvc-ptr-p rnew)
       (equal (subvc-ptr-data ynew)
              (subvc-ptr-data rnew))
       (subvc-same-shape-p ynew yold)
       (equal (subvc-ptr-data xnew)
              (subvc-ptr-data rnew))
       (subvc-same-shape-p xnew xold)
       (subvc-same-shape-p rnew rold)))

(defun subvc-nonoverlap-p (r p rsize psize)
  (or (equal (subvc-ptr-offset r)
             (subvc-ptr-offset p))
      (<= (+ (subvc-ptr-offset r) rsize)
          (subvc-ptr-offset p))
      (<= (+ (subvc-ptr-offset p) psize)
          (subvc-ptr-offset r))))

(defun subvc-alias-map-p (rstate pstate original size)
  (or (equal (subvc-ptr-offset rstate)
             (subvc-ptr-offset pstate))
      (subvc-map-eq-sub-p
       pstate
       original
       (subvc-ptr-offset pstate)
       (+ (subvc-ptr-offset pstate) size))))

(defun subvc-common-invariant-p
  (sy sx r x y rstate xstate ystate index-word borrow)
  (let ((isy (subvc-sint32 sy))
        (isx (subvc-sint32 sx))
        (index (subvc-sint32 index-word)))
    (and (<= isy index)
         (<= index isx)
         (equal
          (- (subvc-value rstate index)
             (* (subvc-ipow (subvc-radix) index)
                borrow))
          (- (subvc-value x index)
             (subvc-value y isy)))
         (subvc-outside-unchanged-p rstate r index)
         (subvc-pelts-equal-p xstate rstate)
         (subvc-pelts-equal-p ystate rstate)
         (subvc-alias-map-p rstate xstate x isx)
         (subvc-alias-map-p rstate ystate y isy)
         (<= 0 borrow)
         (<= borrow 1))))

(defun subvc-first-invariant-p
  (sy sx r x y rstate xstate ystate index-word borrow)
  (and
   (subvc-common-invariant-p
    sy sx r x y rstate xstate ystate index-word borrow)
   (or (equal index-word sx)
       (equal borrow 1))))

(defun subvc-second-invariant-p
  (sy sx r x y rstate xstate ystate index-word borrow)
  (and
   (subvc-common-invariant-p
    sy sx r x y rstate xstate ystate index-word borrow)
   (or (equal index-word sx)
       (equal borrow 0))))

(defun subvc-final-post-p
  (sy sx r x y rstate xstate ystate borrow)
  (let ((isy (subvc-sint32 sy))
        (isx (subvc-sint32 sx)))
    (and
     (equal
      (- (subvc-value rstate isx)
         (* (subvc-ipow (subvc-radix) isx)
            borrow))
      (- (subvc-value x isx)
         (subvc-value y isy)))
     (<= 0 borrow)
     (<= borrow 1)
     (subvc-outside-unchanged-p rstate r isx)
     (subvc-alias-map-p rstate xstate x isx)
     (subvc-alias-map-p rstate ystate y isy))))

(defun-sk subvc-second-next-index-all-p
  (sy sx r x y ynext xnext rnext current-index borrow)
  (forall (next-index)
    (implies
     (and (subvc-bv32-p next-index)
          (equal (subvc-sint32 next-index)
                 (+ (subvc-sint32 current-index) 1)))
     (and
      (<= 0
          (- (subvc-sint32 sx)
             (subvc-sint32 current-index)))
      (< (- (subvc-sint32 sx)
            (subvc-sint32 next-index))
         (- (subvc-sint32 sx)
            (subvc-sint32 current-index)))
      (subvc-second-invariant-p
       sy sx r x y rnext xnext ynext next-index borrow)))))

(defun-sk subvc-second-updated-all-p
  (sy sx r x y ycur xcur rcur current-index borrow)
  (forall (ynext xnext rnext)
    (implies
     (and
      (subvc-transition-p ynext xnext rnext ycur xcur rcur)
      (subvc-updated-p
       rnext
       rcur
       (+ (subvc-ptr-offset rnext)
          (subvc-sint32 current-index))
       (subvc-pelt
        xcur
        (+ (subvc-ptr-offset xcur)
           (subvc-sint32 current-index))))
      (equal
       (subvc-pelt
        rnext
        (+ (subvc-ptr-offset rnext)
           (subvc-sint32 current-index)))
       (subvc-pelt
        xcur
        (+ (subvc-ptr-offset xcur)
           (subvc-sint32 current-index)))))
     (and
      (subvc-int32-bounds-p
       (+ (subvc-sint32 current-index) 1))
      (subvc-second-next-index-all-p
       sy sx r x y ynext xnext rnext current-index borrow)))))

(defun-sk subvc-second-loop-all-p
  (sy sx r x y yprev xprev rprev borrow)
  (forall (index-word ycur xcur rcur)
    (implies
     (and
      (subvc-bv32-p index-word)
      (subvc-transition-p ycur xcur rcur yprev xprev rprev)
      (subvc-second-invariant-p
       sy sx r x y rcur xcur ycur index-word borrow))
     (if (< (subvc-sint32 index-word)
            (subvc-sint32 sx))
         (and
          (subvc-bounds-p xcur (subvc-sint32 index-word))
          (subvc-bounds-p x (subvc-sint32 index-word))
          (subvc-bounds-p rcur (subvc-sint32 index-word))
          (equal (subvc-ptr-writable rcur) t)
          (subvc-second-updated-all-p
           sy sx r x y ycur xcur rcur index-word borrow))
       (subvc-final-post-p
        sy sx r x y rcur xcur ycur borrow)))))

(defun subvc-zero-test-p (word flag)
  (and (booleanp flag)
       (implies (equal word 0)
                (equal flag t))
       (implies (equal flag t)
                (equal word 0))))

(defun-sk subvc-first-zero-test-all-p
  (sy sx r x y ynext xnext rnext xsource next-index
      current-index borrow)
  (forall (zero-flag)
    (implies
     (subvc-zero-test-p
      (subvc-pelt
       xsource
       (+ (subvc-ptr-offset xsource)
          (subvc-sint32 current-index)))
      zero-flag)
     (if (not (equal zero-flag t))
         (and
          (subvc-second-invariant-p
           sy sx r x y rnext xnext ynext
           next-index
           0)
          (subvc-second-loop-all-p
           sy sx r x y ynext xnext rnext 0))
       (and
        (<= 0
            (- (subvc-sint32 sx)
               (subvc-sint32 current-index)))
        (< (- (subvc-sint32 sx)
              (+ (subvc-sint32 current-index) 1))
           (- (subvc-sint32 sx)
              (subvc-sint32 current-index)))
        (subvc-first-invariant-p
         sy sx r x y rnext xnext ynext
         next-index
         borrow))))))

(defun-sk subvc-first-next-index-all-p
  (sy sx r x y ynext xnext rnext xsource current-index borrow)
  (forall (next-index)
    (implies
     (and (subvc-bv32-p next-index)
          (equal (subvc-sint32 next-index)
                 (+ (subvc-sint32 current-index) 1)))
     (subvc-first-zero-test-all-p
      sy sx r x y ynext xnext rnext xsource next-index
      current-index borrow))))

(defun-sk subvc-first-after-write-all-p
  (sy sx r x y ycur xcur rcur current-index borrow result)
  (forall (ynext xnext rnext)
    (implies
     (and
      (subvc-transition-p ynext xnext rnext ycur xcur rcur)
      (subvc-updated-p
       rnext
       rcur
       (+ (subvc-ptr-offset rnext)
          (subvc-sint32 current-index))
       result)
      (equal
       (subvc-pelt
        rnext
        (+ (subvc-ptr-offset rnext)
           (subvc-sint32 current-index)))
       result))
     (and
      (subvc-int32-bounds-p
       (+ (subvc-sint32 current-index) 1))
      (subvc-first-next-index-all-p
       sy sx r x y ynext xnext rnext xcur
       current-index borrow)))))

(defun-sk subvc-first-result-all-p
  (sy sx r x y ycur xcur rcur current-index borrow)
  (forall (result)
    (implies
     (and
      (subvc-bv64-p result)
      (equal
       result
       (mod
        (- (subvc-pelt
            xcur
            (+ (subvc-ptr-offset xcur)
               (subvc-sint32 current-index)))
           1)
        (subvc-radix))))
     (and
      (subvc-bounds-p rcur (subvc-sint32 current-index))
      (equal (subvc-ptr-writable rcur) t)
      (subvc-first-after-write-all-p
       sy sx r x y ycur xcur rcur current-index borrow result)))))

(defun-sk subvc-first-loop-all-p
  (sy sx r x y yprev xprev rprev)
  (forall (index-word borrow ycur xcur rcur)
    (implies
     (and
      (subvc-bv32-p index-word)
      (subvc-bv64-p borrow)
      (subvc-transition-p ycur xcur rcur yprev xprev rprev)
      (subvc-first-invariant-p
       sy sx r x y rcur xcur ycur index-word borrow))
     (if (< (subvc-sint32 index-word)
            (subvc-sint32 sx))
         (and
          (subvc-bounds-p xcur (subvc-sint32 index-word))
          (subvc-bounds-p x (subvc-sint32 index-word))
          (subvc-first-result-all-p
           sy sx r x y ycur xcur rcur index-word borrow))
       (and
        (subvc-second-invariant-p
         sy sx r x y rcur xcur ycur index-word borrow)
        (subvc-second-loop-all-p
         sy sx r x y ycur xcur rcur borrow))))))

(defun-sk subvc-after-zero-test-all-p
  (sy sx r x y ystate xstate rstate borrow)
  (forall (zero-flag)
    (implies
     (subvc-zero-test-p borrow zero-flag)
     (if (not (equal zero-flag t))
         (and
          (subvc-first-invariant-p
           sy sx r x y rstate xstate ystate sy borrow)
          (subvc-first-loop-all-p
           sy sx r x y ystate xstate rstate))
       (and
        (subvc-second-invariant-p
         sy sx r x y rstate xstate ystate sy borrow)
        (subvc-second-loop-all-p
         sy sx r x y ystate xstate rstate borrow))))))

(defun-sk subvc-after-sub-result-all-p
  (sy sx r x y ystate xstate rstate)
  (forall (borrow)
    (implies
     (and
      (subvc-bv64-p borrow)
      (equal
       (- (subvc-value rstate (subvc-sint32 sy))
          (* (subvc-ipow (subvc-radix) (subvc-sint32 sy))
             borrow))
       (- (subvc-value x (subvc-sint32 sy))
          (subvc-value y (subvc-sint32 sy))))
      (<= 0 borrow)
      (<= borrow 1)
      (subvc-outside-unchanged-p
       rstate r (subvc-sint32 sy))
      (subvc-alias-map-p
       rstate xstate x (subvc-sint32 sy))
      (subvc-alias-map-p
       rstate ystate y (subvc-sint32 sy)))
     (subvc-after-zero-test-all-p
      sy sx r x y ystate xstate rstate borrow))))

(defun-sk subvc-after-sub-state-all-p (sy sx r x y)
  (forall (ystate xstate rstate)
    (implies
     (subvc-transition-p ystate xstate rstate y x r)
     (subvc-after-sub-result-all-p
      sy sx r x y ystate xstate rstate))))

(defun-sk sub-Sub-wmpn-subqtvc-statement ()
  (forall (sy sx r x y)
    (implies
     (and
      (subvc-bv32-p sy)
      (subvc-bv32-p sx)
      (subvc-ptr-p r)
      (subvc-ptr-p x)
      (subvc-ptr-p y)
      (<= 0 (subvc-sint32 sy))
      (<= (subvc-sint32 sy)
          (subvc-sint32 sx))
      (subvc-valid-p r (subvc-sint32 sx))
      (subvc-valid-p x (subvc-sint32 sx))
      (subvc-valid-p y (subvc-sint32 sy))
      (subvc-nonoverlap-p
       r x (subvc-sint32 sx) (subvc-sint32 sx))
      (subvc-nonoverlap-p
       r y (subvc-sint32 sx) (subvc-sint32 sy))
      (equal (subvc-ptr-data r)
             (subvc-ptr-data x))
      (equal (subvc-ptr-data r)
             (subvc-ptr-data y))
      (equal (subvc-ptr-writable r) t))
     (and
      (<= 0 (subvc-sint32 sy))
      (subvc-valid-p r (subvc-sint32 sy))
      (subvc-valid-p x (subvc-sint32 sy))
      (subvc-valid-p y (subvc-sint32 sy))
      (subvc-nonoverlap-p
       r x (subvc-sint32 sy) (subvc-sint32 sy))
      (subvc-nonoverlap-p
       r y (subvc-sint32 sy) (subvc-sint32 sy))
      (equal (subvc-ptr-data r)
             (subvc-ptr-data x))
      (equal (subvc-ptr-data r)
             (subvc-ptr-data y))
      (equal (subvc-ptr-writable r) t)
      (subvc-after-sub-state-all-p sy sx r x y)))))

(value-triple :itpeval-statement-checked)
:q
