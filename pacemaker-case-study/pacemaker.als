module pacemaker

sig HeartState {}

sig Heart {
	APulse: HeartState,
	VPulse: HeartState,
	AContract: HeartState,
	VContract: HeartState,
	Recovery: HeartState
} {
	lone this.HeartState
}

sig PacemakerState {}

sig Pacemaker {
	APace: PacemakerState
	VPace: PacemakerState
	Wait: PacemakerState
} {
	lone this.PacemakerState
}

act APace {
	pre = { Heart.Recovery and Pacemaker.Wait }
	post = { Heart.APace and Pacemaker.APulse}
}

act HeartAtriaContract {
	pre = { Heart.APulse }
	post = { Heart.AContract and Pacemaker.Wait}
}

act VPace {
	pre = { Heart.AContract and Pacemaker.Wait }
	....
}
