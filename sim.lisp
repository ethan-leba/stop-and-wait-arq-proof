; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro let-match* (binds body)
  (case-match binds
    ('() body)
    (((pat val) . rst)
     `(let ((greatbadness ,val))
	(case-match greatbadness
	  (,pat (let-match* ,rst ,body)))))))

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state `(sendstate ,data ,nat))

(defdata receiver-state `(recvstate ,data ,nat))

(defdata ack nat)

(defdata packet `(packet ,atom ,ack))

(defdata event-deck (listof nil))
;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state `(sim-state ,sender-state ,receiver-state ,event-deck))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out `(sender-out ,sender-state ,packet))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata receiver-out `(receiver-out ,receiver-state ,ack))

(defdata result (oneof data 'error))

;; ---- Functions ----

(definec sender (sender-state :sender-state) :sender-out
  "This function represents the behavior of the sender in the stop-and-wait ARQ."
  (let-match* ((('sendstate to-send seq-num) sender-state))
    `(sender-out (sendstate ,to-send ,seq-num)
		 (packet ,(car to-send) ,seq-num))))

(definec sender-ack (sender-state :sender-state ack :ack) :sender-state
  (let-match* ((('sendstate to-send seq-num) sender-state))
    `(sendstate ,(cdr to-send) ,(max seq-num ack))))

(definec receiver (receiver-state :receiver-state packet :packet) :receiver-out
  (let-match* ((('recvstate stored &) receiver-state))
    (case-match packet
      (('packet data seq-num)
       `(receiver-out (recvstate ,(app stored (list data)) ,seq-num) ,(1+ seq-num))))))

(definec simulator-state-check (sim :sim-state) :bool
  (let-match* ((('sim-state & & steps) sim))
    (consp steps)))

(definec simulator-step (sim :sim-state) :sim-state
  :ic (simulator-state-check sim)
  (let-match* ((('sim-state ss rs steps) sim)
	       (('sender-out waiting-on-ack-ss packet) (sender ss))
	       (('receiver-out new-rs ack) (receiver rs packet))
	       (new-ss (sender-ack waiting-on-ack-ss ack)))
    `(sim-state ,new-ss ,new-rs ,(cdr steps))))

(check= (simulator-step '(sim-state (sendstate (1 2) 0) (recvstate nil 0) (nil nil nil)))
	'(sim-state (sendstate (2) 1) (recvstate (1) 0) (nil nil)))

(check= (simulator-step '(sim-state (sendstate (1) 0) (recvstate (4 5 6) 0) (nil)))
	'(sim-state (sendstate () 1) (recvstate (4 5 6 1) 0) ()))

(definec simulator-measure (sim :sim-state) :nat
  "Retreives the length of the event-deck."
  (len (cadddr sim)))

(definec simulator (sim :sim-state) :data
  (define (xargs :measure (simulator-measure sim)
		 :termination-method :measure))
  (let-match* ((('sim-state ('sendstate ss &) ('recvstate rs &) steps) sim))
    (cond
     ((or (lendp ss) (lendp steps)) rs)
     (T (simulator (simulator-step sim))))))

(check= (simulator '(sim-state (sendstate (1 2 3) 0) (recvstate (4 5 6) 0) (nil nil nil)))
	'(4 5 6 1 2 3))

(definec simulator* (data :data steps :event-deck) :data
  :ic (>= (len data) (len steps))
  (simulator `(sim-state (sendstate ,data 0) (recvstate nil 0) ,steps)))

(check= (simulator* '(4 5 6) '(nil nil nil))
	'(4 5 6))

;; ---- Proofs ----

(definec take2 (data :tl n :nat) :tl
  :ic (>= (len data) n)
  (if (zp n)
      '()
    (cons (car data) (take2 (cdr data) (1- n)))))

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

(defthm take2-always-a-prefix
  (implies (and (tlp x)
		(natp n)
		(>= (len x) n))
	   (prefixp (take2 x n) x)))

(definec more-data-than-steps (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate ss &) & steps) sim))
    (>= (len ss) (len steps))))

;; Needed for a subgoal of take2-sim-relation
(defthm take2-of-1-is-a-car-list
  (implies (ne-tlp x)
	   (equal (take2 x 1)
		  (list (car x)))))

(defthm take2-sim-relation
  (implies (and (sim-statep sim)
		(simulator-state-check sim)
		(more-data-than-steps sim))
	   (equal (simulator sim)
		  (let-match* ((('sim-state ('sendstate ss &) ('recvstate rs &) steps) sim))
		    (app rs (take2 ss (len steps)))))))

(defthm sim*-equiv-take2
  (implies (and (datap d)
		(event-deckp n)
		(>= (len d) (len n)))
	   (equal (simulator* d n) (take2 d n))))

(defthm data-never-out-of-order
  (implies (and (datap d)
		(event-deckp n)
		(>= (len d) (len n)))
	   (prefixp (simulator* d n) d)))

 
