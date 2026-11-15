;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_loop_inv_2_preserved_goal3:
;; preservation of the idle-core loop invariant under the stated CPU-mask,
;; integer-range, memory validity, framing, layout, separation, and quantified
;; search hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun icp3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun icp3-address-base (address)
  (car address))

(defun icp3-address-offset (address)
  (cdr address))

(defun icp3-shift (address amount)
  (cons
   (icp3-address-base address)
   (+ (icp3-address-offset address) amount)))

;; Conservative interfaces for the arbitrary pointer memory t_2, integer
;; memory t_1, allocation map t, and the fixed source symbols.

(defstub icp3-pointer-memory (address) t)
(defstub icp3-integer-memory (address) t)
(defstub icp3-allocation (index) t)
(defstub icp3-region (base) t)
(defstub icp3-linked-op () t)
(defstub icp3-l-size () t)
(defstub icp3-mask-memory-apply (memory-symbol address) t)
(defstub icp3-mask-pointer-apply (pointer-symbol address) t)
(defstub icp3-l-idle-cpu (index) t)
(defstub icp3-l-sched-group-cpus (address) t)
(defstub icp3-l-sched-group-mask (address) t)
(defstub icp3-l-group-balance-mask (address) t)
(defstub icp3-l-cpu-smt-mask (index) t)

(defun icp3-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk icp3-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (icp3-address-p address)
      (and
       (integerp
        (icp3-mask-memory-apply
         memory-symbol address))
       (icp3-address-p
        (icp3-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (icp3-is-uint8-p
        (icp3-l-idle-cpu index))
       (icp3-address-p
        (icp3-l-cpu-smt-mask index)))))))

(defun-sk icp3-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (icp3-address-p address)
     (equal
      (icp3-mask-memory-apply
       'icp3-zero-memory address)
      0))))

(defun-sk icp3-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (icp3-l-size)))
     (not
      (equal
       (icp3-mask-memory-apply
        memory-symbol
        (icp3-shift
         (icp3-mask-pointer-apply
          pointer-symbol
          (icp3-shift
           (icp3-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk icp3-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (icp3-mask-memory-apply
         memory-symbol
         (icp3-shift
          (icp3-mask-pointer-apply
           pointer-symbol
           (icp3-shift
            (icp3-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (icp3-l-size))
      (<= 0 j)
      (< j (icp3-l-size)))
     (not
      (equal
       (icp3-mask-memory-apply
        memory-symbol
        (icp3-shift
         (icp3-mask-pointer-apply
          pointer-symbol
          (icp3-shift
           (icp3-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk icp3-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (icp3-mask-memory-apply
         memory-symbol
         (icp3-shift
          (icp3-mask-pointer-apply
           pointer-symbol
           (icp3-shift
            (icp3-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (icp3-mask-memory-apply
         memory-symbol
         (icp3-shift
          (icp3-mask-pointer-apply
           pointer-symbol
           (icp3-shift
            (icp3-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (icp3-l-size))
      (<= 0 j)
      (< j (icp3-l-size))
      (<= 0 k)
      (< k (icp3-l-size)))
     (not
      (equal
       (icp3-mask-memory-apply
        memory-symbol
        (icp3-shift
         (icp3-mask-pointer-apply
          pointer-symbol
          (icp3-shift
           (icp3-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun-sk icp3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (icp3-address-p address)
      (and
       (icp3-address-p (icp3-pointer-memory address))
       (integerp (icp3-integer-memory address))
       (icp3-address-p (icp3-l-sched-group-cpus address))
       (icp3-address-p (icp3-l-sched-group-mask address))
       (icp3-address-p (icp3-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (icp3-allocation index))
       (icp3-is-uint8-p (icp3-l-idle-cpu index))
       (icp3-address-p (icp3-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (icp3-region base))))))

(defun icp3-linked-p ()
  (if (icp3-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun icp3-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun icp3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun icp3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun icp3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (icp3-address-base address))
    (<= 0 (icp3-address-offset address))
    (<=
     (+ (icp3-address-offset address) length)
     (icp3-allocation (icp3-address-base address))))))

(defun icp3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (icp3-address-base address)))
    (<= 0 (icp3-address-offset address))
    (<=
     (+ (icp3-address-offset address) length)
     (icp3-allocation (icp3-address-base address))))))

(defun icp3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (icp3-address-base left)
     (icp3-address-base right)))
   (<=
    (+ (icp3-address-offset right) right-length)
    (icp3-address-offset left))
   (<=
    (+ (icp3-address-offset left) left-length)
    (icp3-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk icp3-framed-p ()
  (forall (address)
    (implies
     (icp3-address-p address)
     (<=
      (icp3-region
       (icp3-address-base
        (icp3-pointer-memory address)))
      0))))

;; The existential search condition used by five source hypotheses.

(defun-sk icp3-selected-tail-exists-p (a2 x1)
  (exists (i6)
    (and
     (integerp i6)
     (not
      (equal
       (icp3-integer-memory
        (icp3-shift a2 i6))
       0))
     (< i6 (icp3-l-size))
     (<= x1 i6))))

;; The universal no-selection condition from x_1 through l_size.

(defun-sk icp3-tail-zero-p (a2 x1)
  (forall (i6)
    (implies
     (integerp i6)
     (implies
      (< i6 (icp3-l-size))
      (implies
       (<= x1 i6)
       (equal
        (icp3-integer-memory
         (icp3-shift a2 i6))
        0))))))

;; Every selected position from x_1 below i_4 is zero.

(defun-sk icp3-prefix-zero-p (a2 x1 i4)
  (forall (i6)
    (implies
     (integerp i6)
     (implies
      (< i6 i4)
      (implies
       (<= x1 i6)
       (equal
        (icp3-integer-memory
         (icp3-shift a2 i6))
        0))))))

;; Every selected CPU below i_2 is non-idle.

(defun-sk icp3-selected-cpus-non-idle-p (a2 i2)
  (forall (i6)
    (implies
     (integerp i6)
     (implies
      (not
       (equal
        (icp3-integer-memory
         (icp3-shift a2 i6))
        0))
      (implies
       (<= 0 i6)
       (implies
        (< i6 i2)
        (not
         (equal
          (icp3-l-idle-cpu i6)
          0))))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk icp3-array-layout-p (a)
  (forall (i6)
    (implies
     (integerp i6)
     (let ((a3 (icp3-shift a i6)))
       (implies
        (<= 0 i6)
        (implies
         (< i6 (icp3-l-size))
         (and
          (icp3-valid-rd-p a3 1)
          (icp3-valid-rw-p
           (icp3-shift
            (icp3-pointer-memory
             (icp3-shift a3 0))
            0)
           (icp3-l-size)))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk icp3-separated-from-array-masks-p (mask a)
  (forall (i6)
    (implies
     (integerp i6)
     (implies
      (<= 0 i6)
      (implies
       (< i6 (icp3-l-size))
       (icp3-separated-p
        mask
        (icp3-l-size)
        (icp3-shift
         (icp3-pointer-memory
          (icp3-shift
           (icp3-shift a i6)
           0))
         0)
        (icp3-l-size)))))))

(defun-sk icp3-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (icp3-address-p address)
     (let*
         ((a4 (icp3-l-sched-group-cpus address))
          (a5
           (icp3-shift
            (icp3-pointer-memory
             (icp3-shift a4 0))
            0)))
       (and
        (icp3-valid-rd-p a4 1)
        (icp3-valid-rd-p a5 (icp3-l-size))
        (icp3-separated-from-array-masks-p a5 a))))))

(defun-sk icp3-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (icp3-address-p address)
     (let*
         ((a4 (icp3-l-sched-group-mask address))
          (a5
           (icp3-shift
            (icp3-pointer-memory
             (icp3-shift a4 0))
            0)))
       (and
        (icp3-valid-rd-p a4 1)
        (icp3-valid-rd-p a5 (icp3-l-size))
        (icp3-separated-from-array-masks-p a5 a))))))

(defun-sk icp3-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (icp3-address-p address)
     (let*
         ((a4 (icp3-l-group-balance-mask address))
          (a5
           (icp3-shift
            (icp3-pointer-memory
             (icp3-shift a4 0))
            0)))
       (and
        (icp3-valid-rd-p a4 1)
        (icp3-valid-rd-p a5 (icp3-l-size))
        (icp3-separated-from-array-masks-p a5 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk icp3-cpu-smt-layout-p (a)
  (forall (i6)
    (implies
     (integerp i6)
     (let*
         ((a3 (icp3-l-cpu-smt-mask i6))
          (a4
           (icp3-shift
            (icp3-pointer-memory
             (icp3-shift a3 0))
            0)))
       (implies
        (<= 0 i6)
        (implies
         (< i6 (icp3-l-size))
         (and
          (icp3-valid-rd-p a3 1)
          (icp3-valid-rd-p a4 (icp3-l-size))
          (icp3-separated-from-array-masks-p a4 a))))))))

(defun-sk
    ntp4vc-is-core-idle-loop-inv-2-preserved-goal3-statement ()
  (forall
   (i5 i4 i2 i3 i i1 a)
   (implies
    (and
     (icp3-function-types-p)
     (icp3-scheduler-schema-types-p)
     (icp3-zero-mask-memory-instance-p)
     (icp3-q-mask-refl-p)
     (icp3-q-mask-symm-p)
     (icp3-q-mask-trans-p)
     (integerp (icp3-l-size))
     (< 0 (icp3-l-size))
     (<= (icp3-l-size) 2147483647)
     (integerp i5)
     (integerp i4)
     (integerp i2)
     (integerp i3)
     (integerp i)
     (integerp i1)
     (icp3-address-p a))
    (let*
        ((a1
          (icp3-shift
           (icp3-l-cpu-smt-mask i5)
           0))
         (a2 (icp3-pointer-memory a1))
         (x
          (icp3-integer-memory
           (icp3-shift a2 i4)))
         (x1 (icp3-to-uint32 i2)))
      (implies
       (and
        (not (equal (icp3-l-idle-cpu i5) 0))
        (not
         (equal
          (icp3-integer-memory
           (icp3-shift a2 i3))
          0))
        (<= 0 i)
        (< i (icp3-l-size))
        (<= i3 i1)
        (<= 0 i2)
        (<= 0 i3)
        (<= 0 i5)
        (< i5 (icp3-l-size))
        (<= i2 (icp3-l-size))
        (< (icp3-to-uint32 i4) (icp3-l-size))
        (<= (icp3-region (icp3-address-base a)) 0)
        (icp3-framed-p)
        (icp3-linked-p)
        (icp3-is-uint32-p i)
        (icp3-is-sint32-p i1)
        (icp3-is-sint32-p i2)
        (icp3-is-sint32-p i4)
        (icp3-is-sint32-p i5)
        (icp3-is-sint32-p (+ 1 i1))
        (icp3-valid-rd-p a1 1)
        (icp3-is-uint8-p x)
        (icp3-valid-rd-p
         (icp3-shift a2 0)
         (icp3-l-size))
        (if (equal i5 i4)
            (and
             (equal i5 i1)
             (<= i5 2147483646))
          (and
           (equal i4 i1)
           (not (equal (icp3-l-idle-cpu i4) 0))
           (<= 0 i4)
           (< i4 (icp3-l-size))
           (<= i4 2147483646)))
        (implies
         (icp3-tail-zero-p a2 x1)
         (equal (icp3-l-size) i4))
        (implies
         (icp3-selected-tail-exists-p a2 x1)
         (not (equal x 0)))
        (implies
         (icp3-selected-tail-exists-p a2 x1)
         (< i4 (icp3-l-size)))
        (implies
         (icp3-selected-tail-exists-p a2 x1)
         (and
          (< i4 (icp3-l-size))
          (<= x1 i4)))
        (implies
         (icp3-selected-tail-exists-p a2 x1)
         (icp3-prefix-zero-p a2 x1 i4))
        (icp3-selected-cpus-non-idle-p a2 i2)
        (icp3-array-layout-p a)
        (icp3-sched-group-cpus-layout-p a)
        (icp3-sched-group-mask-layout-p a)
        (icp3-group-balance-mask-layout-p a)
        (icp3-cpu-smt-layout-p a))
       (not
        (equal
         (icp3-l-idle-cpu i3)
         0)))))))

(value-triple :itpeval-statement-checked)

:q
