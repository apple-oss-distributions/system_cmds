//
//  TraceFileAction.h
//  kdprof
//
//  Created by James McIlree on 4/15/13.
//  Copyright (c) 2013 Apple. All rights reserved.
//

#ifndef __kdprof__TraceFileAction__
#define __kdprof__TraceFileAction__

class TraceFileAction : public Action {
    protected:
	std::string _path;
	
    public:
	TraceFileAction(const char* path) : _path(path) {
		ASSERT(Path::is_file(_path, TRUE), "File must exist");
	}

	virtual void execute(Globals& globals);
};

#endif /* defined(__kdprof__TraceFileAction__) */
