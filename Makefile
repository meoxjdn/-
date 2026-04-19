MODULE_NAME := android-wuwa

# 将新的页表引擎编译为模块
obj-m := $(MODULE_NAME).o
$(MODULE_NAME)-objs := kpm_shadow.o

KDIR ?= /lib/modules/$(shell uname -r)/build
PWD := $(shell pwd)

all:
	$(MAKE) -C $(KDIR) M=$(PWD) modules

clean:
	$(MAKE) -C $(KDIR) M=$(PWD) clean
