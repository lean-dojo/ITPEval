;; Statement-only formalization of ntp4vc corpus artifact
;; pearl/multiprecision/div_Div_wmpn_divrem_2qtvc: the verification condition
;; for two-limb multiprecision division, including reciprocal division,
;; quotient storage, remainder storage, and loop-invariant preservation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove proof-builder observation))

(defun ddr2-radix ()
  18446744073709551616)

(defun ddr2-bv32-p (x)
  (and (integerp x)
       (<= 0 x)
       (< x 4294967296)))

(defun ddr2-bv64-p (x)
  (and (integerp x)
       (<= 0 x)
       (< x (ddr2-radix))))

(defun ddr2-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun ddr2-int32-bounds-p (x)
  (and (integerp x)
       (<= -2147483648 x)
       (< x 2147483648)))

(defun ddr2-ipow (base exponent)
  (expt base (nfix exponent)))

; A pointer is (tag data offset min max writable zone).  Data packages an
; independent nonnegative length with a total integer-indexed limb map.  A
; map is represented by an arbitrary base token and explicit update nodes.
(defun ddr2-data-p (data)
  (and (true-listp data)
       (equal (len data) 3)
       (equal (nth 0 data) :ddr2-data)
       (natp (nth 1 data))))

(defun ddr2-ptr-p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (nth 0 p) :ddr2-ptr)
       (ddr2-data-p (nth 1 p))
       (integerp (nth 2 p))
       (integerp (nth 3 p))
       (integerp (nth 4 p))
       (booleanp (nth 5 p))))

(defun ddr2-ptr-data (p)
  (nth 1 p))

(defun ddr2-data-length (p)
  (nth 1 (ddr2-ptr-data p)))

(defun ddr2-data-cells (p)
  (nth 2 (ddr2-ptr-data p)))

(defun ddr2-ptr-offset (p)
  (nth 2 p))

(defun ddr2-ptr-min (p)
  (nth 3 p))

(defun ddr2-ptr-max (p)
  (nth 4 p))

(defun ddr2-ptr-writable (p)
  (nth 5 p))

(defun ddr2-ptr-zone (p)
  (nth 6 p))

(defun ddr2-ptr-map (p)
  (ddr2-data-cells p))

(defun ddr2-map-update (map index value)
  (list :update map index value))

(defstub ddr2-base-map-get (map index) t)

(defun ddr2-map-get (map index)
  (declare (xargs :measure (acl2-count map)))
  (if (and (consp map)
           (equal (car map) :update)
           (consp (cdr map))
           (consp (cddr map))
           (consp (cdddr map)))
      (if (equal index (caddr map))
          (cadddr map)
        (ddr2-map-get (cadr map) index))
    (let ((value (ddr2-base-map-get map index)))
      (if (ddr2-bv64-p value) value 0))))

(defun-sk ddr2-map-equal-p (left right)
  (forall (index)
    (implies (integerp index)
             (equal (ddr2-map-get left index)
                    (ddr2-map-get right index)))))

(defun ddr2-ptr-valid-p (p size)
  (and (ddr2-int32-bounds-p size)
       (<= 0 size)
       (<= 0 (ddr2-ptr-min p))
       (<= (ddr2-ptr-min p)
           (ddr2-ptr-offset p))
       (<= (+ (ddr2-ptr-offset p) size)
           (ddr2-ptr-max p))
       (<= (ddr2-ptr-max p)
           (ddr2-data-length p))))

(defun ddr2-bounds-p (p displacement)
  (and (<= (ddr2-ptr-min p)
           (+ (ddr2-ptr-offset p) displacement))
       (< (+ (ddr2-ptr-offset p) displacement)
          (ddr2-ptr-max p))))

(defun ddr2-inclusive-bounds-p (p displacement)
  (and (<= (ddr2-ptr-min p)
           (+ (ddr2-ptr-offset p) displacement))
       (<= (+ (ddr2-ptr-offset p) displacement)
           (ddr2-ptr-max p))))

(defun ddr2-value-sub (map offset size)
  (declare (xargs :measure (nfix size)))
  (if (zp size)
      0
    (+ (ddr2-map-get map offset)
       (* (ddr2-radix)
          (ddr2-value-sub map (+ offset 1) (- size 1))))))

(defun ddr2-value (p size)
  (ddr2-value-sub (ddr2-ptr-map p)
                  (ddr2-ptr-offset p)
                  size))

(defun ddr2-reciprocal-3by2-p (dinv dh dl)
  (equal
   dinv
   (- (floor (- (ddr2-ipow (ddr2-radix) 3) 1)
             (+ dl (* (ddr2-radix) dh)))
      (ddr2-radix))))

(defun ddr2-same-shape-p (new old)
  (and (equal (ddr2-data-length new)
              (ddr2-data-length old))
       (equal (ddr2-ptr-offset new)
              (ddr2-ptr-offset old))
       (equal (ddr2-ptr-min new)
              (ddr2-ptr-min old))
       (equal (ddr2-ptr-max new)
              (ddr2-ptr-max old))
       (equal (ddr2-ptr-writable new)
              (ddr2-ptr-writable old))
       (equal (ddr2-ptr-zone new)
              (ddr2-ptr-zone old))))

(defun ddr2-shift-copy-p (shifted base displacement)
  (and (equal (ddr2-ptr-offset shifted)
              (+ (ddr2-ptr-offset base) displacement))
       (equal (ddr2-data-length shifted)
              (ddr2-data-length base))
       (ddr2-map-equal-p (ddr2-ptr-map shifted)
                         (ddr2-ptr-map base))
       (equal (ddr2-ptr-data shifted)
              (ddr2-ptr-data base))
       (equal (ddr2-ptr-min shifted)
              (ddr2-ptr-min base))
       (equal (ddr2-ptr-max shifted)
              (ddr2-ptr-max base))
       (equal (ddr2-ptr-zone shifted)
              (ddr2-ptr-zone base))
       (equal (ddr2-ptr-writable shifted)
              (ddr2-ptr-writable base))))

(defun ddr2-remainder-p (low high dl dh)
  (< (+ low (* (ddr2-radix) high))
     (+ dl (* (ddr2-radix) dh))))

(defun ddr2-loop-state-p
  (sx x y qstate qh low high work index)
  (and (<= 0 index)
       (<= index (- (ddr2-sint32 sx) 2))
       (equal (ddr2-ptr-offset work)
              (+ (ddr2-ptr-offset x) index))
       (equal (ddr2-data-length work)
              (ddr2-data-length x))
       (equal (ddr2-ptr-min work)
              (ddr2-ptr-min x))
       (equal (ddr2-ptr-max work)
              (ddr2-ptr-max x))
       (ddr2-map-equal-p (ddr2-ptr-map work)
                         (ddr2-ptr-map x))
       (equal (ddr2-ptr-writable work) t)
       (equal
        (ddr2-value x (ddr2-sint32 sx))
        (+ (* (* (+ (ddr2-value-sub
                     (ddr2-ptr-map qstate)
                     (+ (ddr2-ptr-offset qstate) index)
                     (- (- (ddr2-sint32 sx) 2) index))
                    (* qh
                       (ddr2-ipow
                        (ddr2-radix)
                        (- (- (ddr2-sint32 sx) 2) index))))
                 (ddr2-value y 2))
              (ddr2-ipow (ddr2-radix) index))
           (ddr2-value x index)
           (* (ddr2-ipow (ddr2-radix) index)
              (+ low (* (ddr2-radix) high)))))
       (ddr2-remainder-p
        low high
        (ddr2-map-get (ddr2-ptr-map y)
                      (ddr2-ptr-offset y))
        (ddr2-map-get (ddr2-ptr-map y)
                      (+ (ddr2-ptr-offset y) 1)))))

(defun ddr2-adjust-test-p (dh dl o3 o4)
  (if (<= dh o3)
      (if (< dh o3)
          t
        (if (<= dl o4) t nil))
    nil))

(defun-sk ddr2-borrow-all-p (o4 dl)
  (forall (r0 borrow)
    (implies
     (and (ddr2-bv64-p r0)
          (ddr2-bv64-p borrow)
          (equal (- r0 (* (ddr2-radix) borrow))
                 (- (- o4 dl) 0))
          (<= 0 borrow)
          (<= borrow 1))
     (and (<= 0 borrow)
          (<= borrow 1)))))

(defun-sk ddr2-adjust-true-witness-p (rh rl qh dh dl o3 o4)
  (exists (borrow-low borrow-high)
    (and (ddr2-bv64-p borrow-low)
         (ddr2-bv64-p borrow-high)
         (equal (- rl (* (ddr2-radix) borrow-low))
                (- (- o4 dl) 0))
         (<= 0 borrow-low)
         (<= borrow-low 1)
         (equal (- rh (* (ddr2-radix) borrow-high))
                (- (- o3 dh) borrow-low))
         (<= 0 borrow-high)
         (<= borrow-high 1)
         (equal qh 1))))

(defun-sk ddr2-initial-adjust-witness-p (rh rl qh dh dl o3 o4)
  (exists (selected)
    (and (booleanp selected)
         (equal selected (ddr2-adjust-test-p dh dl o3 o4))
         (if (equal selected t)
             (ddr2-adjust-true-witness-p rh rl qh dh dl o3 o4)
           (and (equal rh o3)
                (equal rl o4)
                (equal qh 0))))))

(defun ddr2-final-result-p (sx x y qh qstate result-state)
  (and
   (equal
    (ddr2-value x (ddr2-sint32 sx))
    (+ (* (+ (ddr2-value qstate (- (ddr2-sint32 sx) 2))
             (* (ddr2-ipow
                 (ddr2-radix)
                 (- (ddr2-sint32 sx) 2))
                qh))
          (ddr2-value y 2))
       (ddr2-value result-state 2)))
   (< (ddr2-value result-state 2)
      (ddr2-value y 2))
   (<= 0 qh)
   (<= qh 1)))

(defun-sk ddr2-final-x2-all-p
  (sx x y qh qstate x1 low)
  (forall (x2)
    (implies
     (and (ddr2-ptr-p x2)
          (ddr2-same-shape-p x2 x1)
          (ddr2-map-equal-p
           (ddr2-ptr-map x2)
           (ddr2-map-update
            (ddr2-ptr-map x1)
            (ddr2-ptr-offset x2)
            low)))
     (ddr2-final-result-p sx x y qh qstate x2))))

(defun-sk ddr2-final-x1-all-p
  (sx x y qh qstate low high)
  (forall (x1)
    (implies
     (and (ddr2-ptr-p x1)
          (ddr2-same-shape-p x1 x)
          (ddr2-map-equal-p
           (ddr2-ptr-map x1)
           (ddr2-map-update
            (ddr2-ptr-map x)
            (+ (ddr2-ptr-offset x1) 1)
            high))
          (equal
           (ddr2-map-get
            (ddr2-ptr-map x1)
            (+ (ddr2-ptr-offset x1) 1))
           high))
     (and
      (ddr2-bounds-p x1 0)
      (equal (ddr2-ptr-writable x1) t)
      (ddr2-final-x2-all-p sx x y qh qstate x1 low)))))

(defun-sk ddr2-next-q2-all-p
  (sx x y qh qstate q1 work i o7 r0 r1 quotient)
  (forall (q2)
    (implies
     (and (ddr2-ptr-p q2)
          (ddr2-same-shape-p q2 q1)
          (ddr2-map-equal-p
           (ddr2-ptr-map q2)
           (ddr2-map-update
            (ddr2-ptr-map q1)
            (+ (ddr2-ptr-offset q2) (ddr2-sint32 o7))
            quotient))
          (equal
           (ddr2-map-get
            (ddr2-ptr-map q2)
            (+ (ddr2-ptr-offset q2) (ddr2-sint32 o7)))
           quotient))
     (and
      (< (ddr2-sint32 o7)
         (ddr2-sint32 i))
      (ddr2-loop-state-p
       sx x y q2 qh r0 r1 work (ddr2-sint32 o7))))))

(defun-sk ddr2-next-o7-all-p
  (sx x y qh qstate q1 work i r0 r1 quotient)
  (forall (o7)
    (implies
     (and (ddr2-bv32-p o7)
          (equal (ddr2-sint32 o7)
                 (- (ddr2-sint32 i) 1)))
     (and
      (ddr2-bounds-p q1 (ddr2-sint32 o7))
      (equal (ddr2-ptr-writable q1) t)
      (ddr2-next-q2-all-p
       sx x y qh qstate q1 work i o7 r0 r1 quotient)))))

(defun-sk ddr2-div-result-all-p
  (sx x y qh qstate q1 work i dinv dh dl current-low current-high)
  (forall (quotient r0 r1)
    (implies
     (and
      (ddr2-bv64-p quotient)
      (ddr2-bv64-p r0)
      (ddr2-bv64-p r1)
      (equal
       (+ (* quotient dl)
          (* (ddr2-radix) quotient dh)
          r0
          (* (ddr2-radix) r1))
       (+ (ddr2-map-get
           (ddr2-ptr-map work)
           (ddr2-ptr-offset work))
          (* (ddr2-radix) current-low)
          (* (ddr2-radix) (ddr2-radix) current-high)))
      (<= 0 (+ r0 (* (ddr2-radix) r1)))
      (< (+ r0 (* (ddr2-radix) r1))
         (+ dl (* (ddr2-radix) dh))))
     (and
      (ddr2-int32-bounds-p (- (ddr2-sint32 i) 1))
      (ddr2-next-o7-all-p
       sx x y qh qstate q1 work i r0 r1 quotient)))))

(defun-sk ddr2-shifted-work-all-p
  (sx x y qh qstate q1 xp i dinv dh dl low high)
  (forall (work)
    (implies
     (and (ddr2-ptr-p work)
          (ddr2-shift-copy-p work xp -1))
     (and
      (ddr2-bounds-p work 0)
      (<= (floor (ddr2-radix) 2) dh)
      (ddr2-reciprocal-3by2-p dinv dh dl)
      (ddr2-remainder-p low high dl dh)
      (ddr2-div-result-all-p
       sx x y qh qstate q1 work i dinv dh dl low high)))))

(defun ddr2-loop-step-p
  (sx x y qh qstate q1 xp i dinv dh dl low high)
  (if (< 0 (ddr2-sint32 i))
      (and
       (ddr2-inclusive-bounds-p xp -1)
       (ddr2-shifted-work-all-p
        sx x y qh qstate q1 xp i dinv dh dl low high))
    (and
     (ddr2-bounds-p x 1)
     (equal (ddr2-ptr-writable x) t)
     (ddr2-final-x1-all-p sx x y qh q1 low high))))

(defun-sk ddr2-loop-all-p
  (sx x y qstate qh dinv dh dl)
  (forall (i low high xp q1)
    (implies
     (and
      (ddr2-bv32-p i)
      (ddr2-bv64-p low)
      (ddr2-bv64-p high)
      (ddr2-ptr-p xp)
      (ddr2-ptr-p q1)
      (ddr2-same-shape-p q1 qstate))
     (implies
      (ddr2-loop-state-p
       sx x y q1 qh low high xp (ddr2-sint32 i))
      (ddr2-loop-step-p
       sx x y qh qstate q1 xp i dinv dh dl low high)))))

(defun-sk ddr2-initial-result-all-p
  (sx x y qstate work index dinv dh dl o3 o4)
  (forall (rh rl qh)
    (implies
     (and
      (ddr2-bv64-p rh)
      (ddr2-bv64-p rl)
      (ddr2-bv64-p qh)
      (ddr2-initial-adjust-witness-p rh rl qh dh dl o3 o4))
     (and
      (ddr2-loop-state-p
       sx x y qstate qh rl rh work (ddr2-sint32 index))
      (ddr2-loop-all-p sx x y qstate qh dinv dh dl)))))

(defun-sk ddr2-dinv-all-p
  (sx x y qstate work index dh dl o3 o4)
  (forall (dinv)
    (implies
     (and (ddr2-bv64-p dinv)
          (ddr2-reciprocal-3by2-p dinv dh dl))
     (and
      (implies
       (ddr2-adjust-test-p dh dl o3 o4)
       (and
        (and (<= 0 0) (<= 0 1))
        (ddr2-borrow-all-p o4 dl)))
      (ddr2-initial-result-all-p
       sx x y qstate work index dinv dh dl o3 o4)))))

(defun-sk ddr2-index-all-p
  (sx x y qstate work dh dl o3 o4)
  (forall (index)
    (implies
     (and (ddr2-bv32-p index)
          (equal (ddr2-sint32 index)
                 (- (ddr2-sint32 sx) 2)))
     (and
      (<= (floor (ddr2-radix) 2) dh)
      (ddr2-dinv-all-p
       sx x y qstate work index dh dl o3 o4)))))

(defun ddr2-loaded-work-p (sx x y qstate work)
  (let* ((dh (ddr2-map-get
              (ddr2-ptr-map y)
              (+ (ddr2-ptr-offset y) 1)))
         (dl (ddr2-map-get
              (ddr2-ptr-map y)
              (ddr2-ptr-offset y)))
         (o3 (ddr2-map-get
              (ddr2-ptr-map work)
              (+ (ddr2-ptr-offset work) 1)))
         (o4 (ddr2-map-get
              (ddr2-ptr-map work)
              (ddr2-ptr-offset work))))
    (and
     (ddr2-bounds-p y 1)
     (ddr2-bounds-p y 0)
     (ddr2-bounds-p work 1)
     (ddr2-bounds-p work 0)
     (ddr2-int32-bounds-p (- (ddr2-sint32 sx) 2))
     (ddr2-index-all-p sx x y qstate work dh dl o3 o4))))

(defun-sk ddr2-work-all-p (sx x y qstate displacement)
  (forall (work)
    (implies
     (and (ddr2-ptr-p work)
          (ddr2-shift-copy-p work x displacement))
     (ddr2-loaded-work-p sx x y qstate work))))

(defun-sk ddr2-displacement-all-p (sx x y qstate)
  (forall (displacement)
    (implies
     (and (ddr2-bv32-p displacement)
          (equal (ddr2-sint32 displacement)
                 (- (ddr2-sint32 sx) 2)))
     (and
      (ddr2-inclusive-bounds-p x (ddr2-sint32 displacement))
      (ddr2-work-all-p
       sx x y qstate (ddr2-sint32 displacement))))))

(defun-sk div-Div-wmpn-divrem-2qtvc-statement ()
  (forall (sx x y q)
    (implies
     (and
      (ddr2-bv32-p sx)
      (ddr2-ptr-p x)
      (ddr2-ptr-p y)
      (ddr2-ptr-p q)
      (<= 2 (ddr2-sint32 sx))
      (ddr2-ptr-valid-p x (ddr2-sint32 sx))
      (ddr2-ptr-valid-p y 2)
      (ddr2-ptr-valid-p q (- (ddr2-sint32 sx) 2))
      (<= (floor (ddr2-radix) 2)
          (ddr2-map-get
           (ddr2-ptr-map y)
           (+ (ddr2-ptr-offset y) 1)))
      (equal (ddr2-ptr-writable q) t)
      (equal (ddr2-ptr-writable x) t))
     (and
      (ddr2-int32-bounds-p (- (ddr2-sint32 sx) 2))
      (ddr2-displacement-all-p sx x y q)))))

(value-triple :itpeval-statement-checked)

:q
