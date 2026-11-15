;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_assert_rte_signed_overflow_goal14:
;; the signed-overflow upper bound for a cpumask-andnot loop index under the
;; stated memory validity, framing, separation, byte-range, and quantified
;; loop-invariant hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun cpa14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun cpa14-address-base (address)
  (car address))

(defun cpa14-address-offset (address)
  (cdr address))

(defun cpa14-shift (address amount)
  (cons
   (cpa14-address-base address)
   (+ (cpa14-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, and the
;; fixed region function, CPU-mask address function, linked predicate, and
;; l_size constant.

(defstub cpa14-t3 (address) t)
(defstub cpa14-t1 (address) t)
(defstub cpa14-t2 (address) t)
(defstub cpa14-allocation (index) t)
(defstub cpa14-region (base) t)
(defstub cpa14-l-cpu-smt-mask (index) t)
(defstub cpa14-l-idle-cpu (index) t)
(defstub cpa14-linked-op () t)
(defstub cpa14-l-size () t)

(defstub cpa14-mask-memory-apply (memory-symbol address) t)
(defstub cpa14-mask-pointer-apply (pointer-symbol address) t)

(defun-sk cpa14-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (cpa14-address-p address)
      (and
       (cpa14-address-p (cpa14-t3 address))
       (integerp (cpa14-t1 address))
       (integerp (cpa14-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (cpa14-allocation index))
       (cpa14-address-p (cpa14-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (cpa14-region base))))))

(defun cpa14-linked-p ()
  (if (cpa14-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), the mathematical
;; unsigned 32-bit conversion on every source integer.

(defun cpa14-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun cpa14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun cpa14-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk cpa14-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (cpa14-address-p address)
      (and
       (integerp
        (cpa14-mask-memory-apply
         memory-symbol address))
       (cpa14-address-p
        (cpa14-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (cpa14-is-uint8-p
        (cpa14-l-idle-cpu index))
       (cpa14-address-p
        (cpa14-l-cpu-smt-mask index)))))))

(defun-sk cpa14-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (cpa14-address-p address)
     (equal
      (cpa14-mask-memory-apply
       'cpa14-zero-memory address)
      0))))

(defun-sk cpa14-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (cpa14-l-size))
       (not
        (equal
         (cpa14-mask-memory-apply
          memory-symbol
          (cpa14-shift
           (cpa14-mask-pointer-apply
            pointer-symbol
            (cpa14-shift
             (cpa14-l-cpu-smt-mask index)
             0))
           index))
         0)))))))

(defun-sk cpa14-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and (integerp i) (integerp j))
     (implies
      (not
       (equal
        (cpa14-mask-memory-apply
         memory-symbol
         (cpa14-shift
          (cpa14-mask-pointer-apply
           pointer-symbol
           (cpa14-shift
            (cpa14-l-cpu-smt-mask j)
            0))
          i))
        0))
      (implies
       (<= 0 i)
       (implies
        (< i (cpa14-l-size))
        (implies
         (<= 0 j)
         (implies
          (< j (cpa14-l-size))
          (not
           (equal
            (cpa14-mask-memory-apply
             memory-symbol
             (cpa14-shift
              (cpa14-mask-pointer-apply
               pointer-symbol
               (cpa14-shift
                (cpa14-l-cpu-smt-mask i)
                0))
              j))
            0))))))))))

(defun-sk cpa14-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and (integerp i) (integerp j) (integerp k))
     (implies
      (not
       (equal
        (cpa14-mask-memory-apply
         memory-symbol
         (cpa14-shift
          (cpa14-mask-pointer-apply
           pointer-symbol
           (cpa14-shift
            (cpa14-l-cpu-smt-mask i)
            0))
          j))
        0))
      (implies
       (not
        (equal
         (cpa14-mask-memory-apply
          memory-symbol
          (cpa14-shift
           (cpa14-mask-pointer-apply
            pointer-symbol
            (cpa14-shift
             (cpa14-l-cpu-smt-mask j)
             0))
           k))
         0))
       (implies
        (<= 0 i)
        (implies
         (< i (cpa14-l-size))
         (implies
          (<= 0 j)
          (implies
           (< j (cpa14-l-size))
           (implies
            (<= 0 k)
            (implies
             (< k (cpa14-l-size))
             (not
              (equal
               (cpa14-mask-memory-apply
                memory-symbol
                (cpa14-shift
                 (cpa14-mask-pointer-apply
                  pointer-symbol
                  (cpa14-shift
                   (cpa14-l-cpu-smt-mask i)
                   0))
                 k))
               0)))))))))))))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun cpa14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (cpa14-address-base address))
    (<= 0 (cpa14-address-offset address))
    (<=
     (+ (cpa14-address-offset address) length)
     (cpa14-allocation (cpa14-address-base address))))))

(defun cpa14-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (cpa14-address-base address)))
    (<= 0 (cpa14-address-offset address))
    (<=
     (+ (cpa14-address-offset address) length)
     (cpa14-allocation (cpa14-address-base address))))))

(defun cpa14-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (cpa14-address-base left)
     (cpa14-address-base right)))
   (<=
    (+ (cpa14-address-offset right) right-length)
    (cpa14-address-offset left))
   (<=
    (+ (cpa14-address-offset left) left-length)
    (cpa14-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_3.

(defun-sk cpa14-framed-p ()
  (forall (address)
    (implies
     (cpa14-address-p address)
     (<=
      (cpa14-region
       (cpa14-address-base (cpa14-t3 address)))
      0))))

;; This is the exact havoc_access value for
;; havoc t_1 t_2 protected-start protected-length at query.

(defun cpa14-havoc-value
    (protected-start protected-length query)
  (if
      (cpa14-separated-p
       query 1 protected-start protected-length)
      (cpa14-t2 query)
    (cpa14-t1 query)))

;; Preserve the source universal separation condition for every integer i_1
;; in [0, l_size).

(defun-sk cpa14-mask-separated-p (a12)
  (forall (i1)
    (implies
     (integerp i1)
     (implies
      (<= 0 i1)
      (implies
       (< i1 (cpa14-l-size))
       (cpa14-separated-p
        a12
        (cpa14-l-size)
        (cpa14-shift
         (cpa14-t3
          (cpa14-shift (cpa14-l-cpu-smt-mask i1) 0))
         0)
        (cpa14-l-size)))))))

;; Preserve the source universal agreement between the havoced memory and t_2
;; from the current index through the end of the mask.

(defun-sk cpa14-tail-havoc-agreement-p (a11 i)
  (forall (i1)
    (implies
     (integerp i1)
     (implies
      (<= i i1)
      (implies
       (< i1 (cpa14-l-size))
       (let ((a17 (cpa14-shift a11 i1)))
         (iff
          (not
           (equal
            (cpa14-havoc-value
             a11
             (cpa14-l-size)
             a17)
            0))
          (not (equal (cpa14-t2 a17) 0)))))))))

;; Preserve the source universal loop invariant over every earlier integer
;; index i_1.

(defun-sk cpa14-prefix-invariant-p (a6 a8 a11 i)
  (forall (i1)
    (implies
     (integerp i1)
     (implies
      (<= 0 i1)
      (implies
       (< i1 i)
       (iff
        (and
         (equal (cpa14-t2 (cpa14-shift a6 i1)) 0)
         (not
          (equal
           (cpa14-t2 (cpa14-shift a8 i1))
           0)))
        (not
         (equal
          (cpa14-havoc-value
           a11
           (cpa14-l-size)
           (cpa14-shift a11 i1))
          0))))))))

(defun-sk
    ntp4vc-cpumask-andnot-assert-rte-signed-overflow-goal14-statement ()
  (forall
   (a1 a2 a i)
   (implies
    (and
     (cpa14-function-types-p)
     (cpa14-scheduler-schema-types-p)
     (cpa14-zero-mask-memory-instance-p)
     (cpa14-q-mask-refl-p)
     (cpa14-q-mask-symm-p)
     (cpa14-q-mask-trans-p)
     (integerp (cpa14-l-size))
     (< 0 (cpa14-l-size))
     (<= (cpa14-l-size) 2147483647)
     (cpa14-address-p a1)
     (cpa14-address-p a2)
     (cpa14-address-p a)
     (integerp i))
    (let*
        ((a3 (cpa14-shift a1 0))
         (a4 (cpa14-shift a2 0))
         (a5 (cpa14-shift a 0))
         (a6 (cpa14-t3 a5))
         (a7 (cpa14-shift a6 0))
         (a8 (cpa14-t3 a3))
         (a9 (cpa14-shift a8 0))
         (a10 (cpa14-shift a8 i))
         (a11 (cpa14-t3 a4))
         (a12 (cpa14-shift a11 0))
         (a14 (cpa14-shift a6 i))
         (a15
          (cpa14-havoc-value
           a12
           (cpa14-l-size)
           a14))
         (a16
          (cpa14-havoc-value
           a12
           (cpa14-l-size)
           a10)))
      (implies
       (and
        (not (equal (cons 0 0) a2))
        (not
         (equal
          (cpa14-to-uint32 i)
          (cpa14-l-size)))
        (<= 0 i)
        (<= i (cpa14-l-size))
        (<= (cpa14-region (cpa14-address-base a)) 0)
        (<= (cpa14-region (cpa14-address-base a1)) 0)
        (<= (cpa14-region (cpa14-address-base a2)) 0)
        (cpa14-framed-p)
        (cpa14-linked-p)
        (cpa14-is-sint32-p i)
        (cpa14-valid-rd-p a 1)
        (cpa14-valid-rd-p a1 1)
        (cpa14-valid-rd-p a2 1)
        (cpa14-valid-rd-p a3 1)
        (cpa14-valid-rd-p a4 1)
        (cpa14-valid-rd-p a7 (cpa14-l-size))
        (cpa14-valid-rd-p a9 (cpa14-l-size))
        (cpa14-valid-rd-p a10 1)
        (cpa14-valid-rw-p a12 (cpa14-l-size))
        (cpa14-valid-rw-p (cpa14-shift a11 i) 1)
        (cpa14-is-uint8-p a15)
        (cpa14-is-uint8-p a16)
        (implies
         (not (equal a2 a))
         (cpa14-separated-p
          a12 (cpa14-l-size) a7 (cpa14-l-size)))
        (implies
         (not (equal a2 a1))
         (cpa14-separated-p
          a12 (cpa14-l-size) a9 (cpa14-l-size)))
        (or (equal a16 0) (equal a16 1))
        (or
         (equal a16 0)
         (and
          (cpa14-valid-rd-p a5 1)
          (cpa14-valid-rd-p a14 1)
          (or (equal a15 0) (equal a15 1))))
        (cpa14-mask-separated-p a12)
        (cpa14-tail-havoc-agreement-p a11 i)
        (cpa14-prefix-invariant-p a6 a8 a11 i))
       (<= i 2147483646))))))

(value-triple :itpeval-statement-checked)

:q
