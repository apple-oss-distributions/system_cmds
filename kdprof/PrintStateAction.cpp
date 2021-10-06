//
//  PrintStateAction.cpp
//  kdprof
//
//  Created by James McIlree on 4/17/13.
//  Copyright (c) 2013 Apple. All rights reserved.
//

#include "global.h"

void PrintStateAction::execute(Globals& globals) {
	printf("\n");
	KDBG::state().print();
	printf("\n");
}
